use core::{
  fmt,
  mem::{self, MaybeUninit},
  ptr::{self, NonNull},
  slice,
};

use crossbeam_utils::Backoff;

use super::{common::*, sealed::Sealed, *};

#[allow(unused_imports)]
use std::boxed::Box;

#[cfg(feature = "std")]
type Memory =
  super::memory::Memory<AtomicUsize, std::sync::Arc<std::path::PathBuf>, sealed::Header>;

#[cfg(not(feature = "std"))]
type Memory = super::memory::Memory<AtomicUsize, std::sync::Arc<()>, sealed::Header>;

const SEGMENT_NODE_SIZE: usize = mem::size_of::<SegmentNode>();
const REMOVED_SEGMENT_NODE: u32 = 0;

mod sealed {
  use super::*;

  #[derive(Debug)]
  #[repr(C, align(8))]
  pub struct Header {
    /// The sentinel node for the ordered free list.
    pub(super) sentinel: SegmentNode,
    pub(super) allocated: AtomicU32,
    pub(super) min_segment_size: AtomicU32,
    pub(super) discarded: AtomicU32,
  }

  impl super::super::sealed::Header for Header {
    #[inline]
    fn new(size: u32, min_segment_size: u32) -> Self {
      Self {
        allocated: AtomicU32::new(size),
        sentinel: SegmentNode::sentinel(),
        min_segment_size: AtomicU32::new(min_segment_size),
        discarded: AtomicU32::new(0),
      }
    }

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[inline]
    fn load_allocated(&self) -> u32 {
      self.allocated.load(Ordering::Acquire)
    }

    #[inline]
    fn load_min_segment_size(&self) -> u32 {
      self.min_segment_size.load(Ordering::Acquire)
    }
  }
}

#[repr(transparent)]
struct SegmentNode {
  /// The first 32 bits are the size of the memory,
  /// the last 32 bits are the offset of the next segment node.
  size_and_next: AtomicU64,
}

impl core::fmt::Debug for SegmentNode {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (offset, next) = decode_segment_node(self.size_and_next.load(Ordering::Acquire));
    f.debug_struct("SegmentNode")
      .field("offset", &offset)
      .field("next", &next)
      .finish()
  }
}

impl core::ops::Deref for SegmentNode {
  type Target = AtomicU64;

  #[inline]
  fn deref(&self) -> &Self::Target {
    &self.size_and_next
  }
}

impl SegmentNode {
  #[inline]
  fn sentinel() -> Self {
    Self {
      size_and_next: AtomicU64::new(encode_segment_node(
        SENTINEL_SEGMENT_NODE_OFFSET,
        SENTINEL_SEGMENT_NODE_OFFSET,
      )),
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Segment {
  ptr: *mut u8,
  ptr_offset: u32,
  data_offset: u32,
  data_size: u32,
}

impl Segment {
  /// ## Safety
  /// - offset must be a well-aligned and in-bounds `AtomicU64` pointer.
  #[inline]
  unsafe fn from_offset(arena: &Arena, offset: u32, data_size: u32) -> Self {
    Self {
      ptr: arena.ptr,
      ptr_offset: offset,
      data_offset: offset + SEGMENT_NODE_SIZE as u32,
      data_size,
    }
  }

  #[inline]
  fn as_ref(&self) -> &SegmentNode {
    // Safety: when constructing the Segment, we have checked the ptr_offset is in bounds and well-aligned.
    unsafe {
      let ptr = self.ptr.add(self.ptr_offset as usize);
      &*ptr.cast::<SegmentNode>()
    }
  }

  #[inline]
  fn update_next_node(&self, next: u32) {
    self
      .as_ref()
      .store(encode_segment_node(self.data_size, next), Ordering::Release);
  }
}

/// Arena should be lock-free
pub struct Arena {
  ptr: *mut u8,
  data_offset: u32,
  reserved: usize,
  flag: MemoryFlags,
  max_retries: u8,
  inner: NonNull<Memory>,
  unify: bool,
  magic_version: u16,
  version: u16,
  ro: bool,
  cap: u32,
  freelist: Freelist,
  page_size: u32,
}

impl fmt::Debug for Arena {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let header = self.header();
    let allocated = header.allocated.load(Ordering::Acquire);

    // Safety:
    // The ptr is always non-null, we only deallocate it when the ARENA is dropped.
    let data = unsafe { slice::from_raw_parts(self.ptr, (allocated - self.data_offset) as usize) };

    f.debug_struct("Arena")
      .field("cap", &self.cap)
      .field("header", header)
      .field("data", &data)
      .finish()
  }
}

impl Clone for Arena {
  fn clone(&self) -> Self {
    unsafe {
      let memory = self.inner.as_ref();

      let old_size = memory.refs().fetch_add(1, Ordering::Release);
      if old_size > usize::MAX >> 1 {
        abort();
      }

      // Safety:
      // The ptr is always non-null, and the data is only deallocated when the
      // last Arena is dropped.
      Self {
        reserved: self.reserved,
        max_retries: self.max_retries,
        flag: self.flag,
        magic_version: self.magic_version,
        version: self.version,
        ptr: self.ptr,
        data_offset: self.data_offset,
        ro: self.ro,
        inner: self.inner,
        unify: self.unify,
        cap: self.cap,
        freelist: self.freelist,
        page_size: self.page_size,
      }
    }
  }
}

impl From<Memory> for Arena {
  fn from(memory: Memory) -> Self {
    let ptr = memory.as_mut_ptr();

    Self {
      freelist: memory.freelist(),
      reserved: memory.reserved(),
      cap: memory.cap(),
      flag: memory.flag(),
      unify: memory.unify(),
      magic_version: memory.magic_version(),
      version: memory.version(),
      ptr,
      ro: memory.read_only(),
      max_retries: memory.maximum_retries(),
      data_offset: memory.data_offset() as u32,
      inner: unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(memory)) as _) },
      page_size: *PAGE_SIZE,
    }
  }
}

impl Sealed for Arena {
  type Header = sealed::Header;
  type RefCounter = AtomicUsize;
  #[cfg(feature = "std")]
  type PathRefCounter = std::sync::Arc<std::path::PathBuf>;

  #[cfg(not(feature = "std"))]
  type PathRefCounter = std::sync::Arc<()>;
}

impl Allocator for Arena {
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  type Path = std::sync::Arc<std::path::PathBuf>;

  #[inline]
  fn reserved_bytes(&self) -> usize {
    self.reserved
  }

  #[inline]
  fn reserved_slice(&self) -> &[u8] {
    if self.reserved == 0 {
      return &[];
    }

    // Safety: the ptr is always non-null.
    unsafe { slice::from_raw_parts(self.ptr, self.reserved) }
  }

  #[inline]
  unsafe fn reserved_slice_mut(&self) -> &mut [u8] {
    if self.reserved == 0 {
      return &mut [];
    }

    if self.ro {
      panic!("ARENA is read-only");
    }

    slice::from_raw_parts_mut(self.ptr, self.reserved)
  }

  #[inline]
  unsafe fn alloc<T>(&self) -> Result<RefMut<'_, T, Self>, Error> {
    if mem::size_of::<T>() == 0 {
      return Ok(RefMut::new_zst(self));
    }

    let allocated = self
      .alloc_in::<T>()?
      .expect("allocated size is not zero, but get None");
    let ptr = unsafe { self.get_aligned_pointer_mut::<T>(allocated.memory_offset as usize) };
    if mem::needs_drop::<T>() {
      unsafe {
        let ptr: *mut MaybeUninit<T> = ptr.as_ptr().cast();
        ptr::write(ptr, MaybeUninit::uninit());

        Ok(RefMut::new(ptr::read(ptr), allocated, self))
      }
    } else {
      Ok(RefMut::new_inline(ptr, allocated, self))
    }
  }

  #[inline]
  fn alloc_aligned_bytes<T>(&self, size: u32) -> Result<BytesRefMut<'_, Self>, Error> {
    self.alloc_aligned_bytes_in::<T>(size).map(|a| match a {
      None => BytesRefMut::null(self),
      Some(allocated) => unsafe { BytesRefMut::new(self, allocated) },
    })
  }

  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // #[inline]
  // fn alloc_aligned_bytes_within_page<T>(&self, size: u32) -> Result<BytesRefMut<'_, Self>, Error> {
  //   self
  //     .alloc_aligned_bytes_within_page_in::<T>(size)
  //     .map(|a| match a {
  //       None => BytesRefMut::null(self),
  //       Some(allocated) => unsafe { BytesRefMut::new(self, allocated) },
  //     })
  // }

  #[inline]
  fn alloc_bytes(&self, size: u32) -> Result<BytesRefMut<'_, Self>, Error> {
    self.alloc_bytes_in(size).map(|a| match a {
      None => BytesRefMut::null(self),
      Some(allocated) => unsafe { BytesRefMut::new(self, allocated) },
    })
  }

  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // #[inline]
  // fn alloc_bytes_within_page(&self, size: u32) -> Result<BytesRefMut<'_, Self>, Error> {
  //   self.alloc_bytes_within_page_in(size).map(|a| match a {
  //     None => BytesRefMut::null(self),
  //     Some(allocated) => unsafe { BytesRefMut::new(self, allocated) },
  //   })
  // }

  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // #[inline]
  // unsafe fn alloc_within_page<T>(&self) -> Result<RefMut<'_, T, Self>, Error> {
  //   if mem::size_of::<T>() == 0 {
  //     return Ok(RefMut::new_zst(self));
  //   }

  //   let allocated = self
  //     .alloc_within_page_in::<T>()?
  //     .expect("allocated size is not zero, but get None");
  //   let ptr = unsafe { self.get_aligned_pointer_mut::<T>(allocated.memory_offset as usize) };
  //   if mem::needs_drop::<T>() {
  //     unsafe {
  //       let ptr: *mut MaybeUninit<T> = ptr.as_ptr().cast();
  //       ptr::write(ptr, MaybeUninit::uninit());

  //       Ok(RefMut::new(ptr::read(ptr), allocated, self))
  //     }
  //   } else {
  //     Ok(RefMut::new_inline(ptr, allocated, self))
  //   }
  // }

  #[inline]
  fn allocated(&self) -> usize {
    self.header().allocated.load(Ordering::Acquire) as usize
  }

  #[inline]
  fn raw_mut_ptr(&self) -> *mut u8 {
    self.ptr
  }

  #[inline]
  fn raw_ptr(&self) -> *const u8 {
    self.ptr
  }

  #[inline]
  fn capacity(&self) -> usize {
    self.cap as usize
  }

  #[inline]
  fn unify(&self) -> bool {
    // Safety: the inner is always non-null.
    unsafe { self.inner.as_ref().unify() }
  }

  unsafe fn clear(&self) -> Result<(), Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let memory = &mut *self.inner.as_ptr();
    memory.clear();

    Ok(())
  }

  #[inline]
  fn data_offset(&self) -> usize {
    self.data_offset as usize
  }

  #[inline]
  unsafe fn dealloc(&self, offset: u32, size: u32) -> bool {
    // first try to deallocate the memory back to the main memory.
    let header = self.header();
    // if the offset + size is the current allocated size, then we can deallocate the memory back to the main memory.
    if header
      .allocated
      .compare_exchange(offset + size, offset, Ordering::SeqCst, Ordering::Relaxed)
      .is_ok()
    {
      return true;
    }

    match self.freelist {
      Freelist::None => {
        self.increase_discarded(size);
        true
      }
      Freelist::Optimistic => self.optimistic_dealloc(offset, size),
      Freelist::Pessimistic => self.pessimistic_dealloc(offset, size),
    }
  }

  #[inline]
  fn discard_freelist(&self) -> Result<u32, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    Ok(match self.freelist {
      Freelist::None => 0,
      _ => self.discard_freelist_in(),
    })
  }

  #[inline]
  fn discarded(&self) -> u32 {
    self.header().discarded.load(Ordering::Acquire)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().flush() }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_async(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().flush_async() }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    if self.is_map_file() {
      if len == 0 {
        return Ok(());
      }

      let page_size = (*PAGE_SIZE) as usize;

      // Calculate start page
      let start_page_offset = (offset / page_size) * page_size;

      // Calculate end page. The end offset is the last byte that needs to be flushed.
      let end_offset = offset + len - 1;
      let end_page_offset = ((end_offset / page_size) + 1) * page_size;

      // Check if the end of the last page exceeds the capacity of the memory map
      let end_flush_offset = end_page_offset.min(self.cap as usize);

      // Ensure that the flush does not start beyond the capacity
      if start_page_offset >= self.cap as usize {
        return Err(std::io::Error::new(
          std::io::ErrorKind::InvalidInput,
          "Offset is out of bounds",
        ));
      }

      unsafe {
        return self
          .inner
          .as_ref()
          .flush_range(start_page_offset, end_flush_offset - start_page_offset);
      }
    }

    Ok(())
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_async_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    if self.is_map_file() {
      if len == 0 {
        return Ok(());
      }

      let page_size = (*PAGE_SIZE) as usize;

      // Calculate start page
      let start_page_offset = (offset / page_size) * page_size;

      // Calculate end page. The end offset is the last byte that needs to be flushed.
      let end_offset = offset + len - 1;
      let end_page_offset = ((end_offset / page_size) + 1) * page_size;

      // Check if the end of the last page exceeds the capacity of the memory map
      let end_flush_offset = end_page_offset.min(self.cap as usize);

      // Ensure that the flush does not start beyond the capacity
      if start_page_offset >= self.cap as usize {
        return Err(std::io::Error::new(
          std::io::ErrorKind::InvalidInput,
          "Offset is out of bounds",
        ));
      }

      unsafe {
        return self
          .inner
          .as_ref()
          .flush_async_range(start_page_offset, end_flush_offset - start_page_offset);
      }
    }

    Ok(())
  }

  #[inline]
  fn increase_discarded(&self, size: u32) {
    #[cfg(feature = "tracing")]
    tracing::debug!("discard {size} bytes");

    self.header().discarded.fetch_add(size, Ordering::Release);
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn is_map(&self) -> bool {
    self.flag.contains(MemoryFlags::MMAP)
  }

  #[inline]
  fn is_ondisk(&self) -> bool {
    self.flag.contains(MemoryFlags::ON_DISK)
  }

  #[inline]
  fn is_inmemory(&self) -> bool {
    !self.flag.contains(MemoryFlags::ON_DISK)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn lock_exclusive(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().lock_exclusive() }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn lock_shared(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().lock_shared() }
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.magic_version
  }

  #[inline]
  fn minimum_segment_size(&self) -> u32 {
    self.header().min_segment_size.load(Ordering::Acquire)
  }

  #[inline]
  fn set_minimum_segment_size(&self, size: u32) {
    self
      .header()
      .min_segment_size
      .store(size, Ordering::Release);
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn path(&self) -> Option<&Self::PathRefCounter> {
    // Safety: the inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { self.inner.as_ref().path() }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  unsafe fn mlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    #[cfg(not(windows))]
    unsafe {
      self.inner.as_ref().mlock(offset, len)
    }

    #[cfg(windows)]
    Ok(())
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  unsafe fn munlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    #[cfg(not(windows))]
    unsafe {
      self.inner.as_ref().munlock(offset, len)
    }

    #[cfg(windows)]
    Ok(())
  }

  #[inline]
  unsafe fn offset(&self, ptr: *const u8) -> usize {
    let offset = ptr.offset_from(self.ptr);
    offset as usize
  }

  #[inline]
  fn page_size(&self) -> usize {
    self.page_size as usize
  }

  #[inline]
  fn read_only(&self) -> bool {
    self.ro
  }

  #[inline]
  fn refs(&self) -> usize {
    unsafe { self.inner.as_ref().refs().load(Ordering::Acquire) }
  }

  #[inline]
  fn remaining(&self) -> usize {
    (self.cap as usize).saturating_sub(self.allocated())
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn remove_on_drop(&self, remove_on_drop: bool) {
    // Safety: the inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { self.inner.as_ref().set_remove_on_drop(remove_on_drop) }
  }

  unsafe fn rewind(&self, pos: ArenaPosition) {
    let header = self.header();
    let allocated = header.allocated.load(Ordering::Acquire);
    let data_offset = self.data_offset;
    let cap = self.cap;
    let final_offset = match pos {
      ArenaPosition::Start(offset) => offset.max(data_offset).min(cap),
      ArenaPosition::Current(offset) => {
        let offset = allocated as i64 + offset;
        #[allow(clippy::comparison_chain)]
        if offset > 0 {
          if offset >= (cap as i64) {
            cap
          } else {
            let offset = offset as u32;
            offset.max(data_offset).min(cap)
          }
        } else if offset < 0 {
          data_offset
        } else {
          return;
        }
      }
      ArenaPosition::End(offset) => match cap.checked_sub(offset) {
        Some(val) => val.max(data_offset),
        None => data_offset,
      },
    };

    header.allocated.store(final_offset, Ordering::Release);
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn try_lock_exclusive(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().try_lock_exclusive() }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn try_lock_shared(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().try_lock_shared() }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn unlock(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().unlock() }
  }

  #[inline]
  fn version(&self) -> u16 {
    self.version
  }
}

unsafe impl Send for Arena {}
unsafe impl Sync for Arena {}

impl Arena {
  #[inline]
  fn header(&self) -> &sealed::Header {
    // Safety:
    // The inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { (*self.inner.as_ptr()).header() }
  }
}

impl Arena {
  /// Returns the free list position to insert the value.
  /// - `None` means that we should insert to the head.
  /// - `Some(offset)` means that we should insert after the offset. offset -> new -> next
  fn find_position(&self, val: u32, check: impl Fn(u32, u32) -> bool) -> (u64, &AtomicU64) {
    let header = self.header();
    let mut current: &AtomicU64 = &header.sentinel;
    let mut current_node = current.load(Ordering::Acquire);
    let (mut current_node_size, mut next_offset) = decode_segment_node(current_node);
    let backoff = Backoff::new();
    loop {
      // the list is empty
      if current_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && next_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return (current_node, current);
      }

      // the current is marked as remove and the next is the tail.
      if current_node_size == REMOVED_SEGMENT_NODE && next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return (current_node, current);
      }

      if current_node_size == REMOVED_SEGMENT_NODE {
        current = if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
          backoff.snooze();
          &header.sentinel
        } else {
          self.get_segment_node(next_offset)
        };
        current_node = current.load(Ordering::Acquire);
        (current_node_size, next_offset) = decode_segment_node(current_node);
        continue;
      }

      // the next is the tail, then we should insert the value after the current node.
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return (current_node, current);
      }

      let next = self.get_segment_node(next_offset);
      let next_node = next.load(Ordering::Acquire);
      let (next_node_size, next_next_offset) = decode_segment_node(next_node);
      if next_node_size == REMOVED_SEGMENT_NODE {
        backoff.snooze();
        continue;
      }

      if check(val, next_node_size) {
        return (current_node, current);
      }

      current = next;
      current_node = next_node;
      current_node_size = next_node_size;
      next_offset = next_next_offset;
    }
  }

  #[allow(clippy::type_complexity)]
  fn find_prev_and_next(
    &self,
    val: u32,
    check: impl Fn(u32, u32) -> bool,
  ) -> Option<((u64, &AtomicU64), (u64, &AtomicU64))> {
    let header = self.header();
    let mut current: &AtomicU64 = &header.sentinel;
    let mut current_node = current.load(Ordering::Acquire);
    let (mut current_node_size, mut next_offset) = decode_segment_node(current_node);
    let backoff = Backoff::new();
    loop {
      // the list is empty
      if current_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && next_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return None;
      }

      // the current is marked as remove and the next is the tail.
      if current_node_size == REMOVED_SEGMENT_NODE && next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return None;
      }

      if current_node_size == REMOVED_SEGMENT_NODE {
        current = if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
          return None;
        } else {
          self.get_segment_node(next_offset)
        };
        current_node = current.load(Ordering::Acquire);
        (current_node_size, next_offset) = decode_segment_node(current_node);
        continue;
      }

      // the next is the tail
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return None;
      }

      let next = self.get_segment_node(next_offset);
      let next_node = next.load(Ordering::Acquire);
      let (next_node_size, next_next_offset) = decode_segment_node(next_node);

      if check(val, next_node_size) {
        if next_node_size == REMOVED_SEGMENT_NODE {
          backoff.snooze();
          continue;
        }

        return Some(((current_node, current), (next_node, next)));
      }

      current = self.get_segment_node(next_offset);
      current_node = next_node;
      current_node_size = next_node_size;
      next_offset = next_next_offset;
    }
  }

  fn optimistic_dealloc(&self, offset: u32, size: u32) -> bool {
    // check if we have enough space to allocate a new segment in this segment.
    let Some(segment_node) = self.try_new_segment(offset, size) else {
      return false;
    };

    let backoff = Backoff::new();

    loop {
      let (current_node_size_and_next_node_offset, current) = self
        .find_position(segment_node.data_size, |val, next_node_size| {
          val >= next_node_size
        });
      let (node_size, next_node_offset) =
        decode_segment_node(current_node_size_and_next_node_offset);

      if node_size == REMOVED_SEGMENT_NODE {
        // wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      if segment_node.ptr_offset == next_node_offset {
        // we found ourselves, then we need to refind the position.
        backoff.snooze();
        continue;
      }

      segment_node.update_next_node(next_node_offset);

      match current.compare_exchange(
        current_node_size_and_next_node_offset,
        encode_segment_node(node_size, segment_node.ptr_offset),
        Ordering::AcqRel,
        Ordering::Relaxed,
      ) {
        Ok(_) => {
          #[cfg(feature = "tracing")]
          tracing::debug!(
            "create segment node ({} bytes) at {}, next segment {next_node_offset}",
            segment_node.data_size,
            segment_node.ptr_offset
          );

          self.increase_discarded(segment_node.data_offset - segment_node.ptr_offset);
          return true;
        }
        Err(current) => {
          let (size, _) = decode_segment_node(current);
          // the current is removed from the list, then we need to refind the position.
          if size == REMOVED_SEGMENT_NODE {
            // wait other thread to make progress.
            backoff.snooze();
          } else {
            backoff.spin();
          }
        }
      }
    }
  }

  fn pessimistic_dealloc(&self, offset: u32, size: u32) -> bool {
    // check if we have enough space to allocate a new segment in this segment.
    let Some(segment_node) = self.try_new_segment(offset, size) else {
      return false;
    };

    let backoff = Backoff::new();

    loop {
      let (current_node_size_and_next_node_offset, current) = self
        .find_position(segment_node.data_size, |val, next_node_size| {
          val <= next_node_size
        });
      let (node_size, next_node_offset) =
        decode_segment_node(current_node_size_and_next_node_offset);

      if node_size == REMOVED_SEGMENT_NODE {
        // wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      if segment_node.ptr_offset == next_node_offset {
        // we found ourselves, then we need to refind the position.
        backoff.snooze();
        continue;
      }

      segment_node.update_next_node(next_node_offset);

      match current.compare_exchange(
        current_node_size_and_next_node_offset,
        encode_segment_node(node_size, segment_node.ptr_offset),
        Ordering::AcqRel,
        Ordering::Relaxed,
      ) {
        Ok(_) => {
          #[cfg(feature = "tracing")]
          tracing::debug!(
            "create segment node ({} bytes) at {}, next segment {next_node_offset}",
            segment_node.data_size,
            segment_node.ptr_offset
          );

          self.increase_discarded(segment_node.data_offset - segment_node.ptr_offset);
          return true;
        }
        Err(current) => {
          let (size, _) = decode_segment_node(current);
          // the current is removed from the list, then we need to refind the position.
          if size == REMOVED_SEGMENT_NODE {
            // wait other thread to make progress.
            backoff.snooze();
          } else {
            backoff.spin();
          }
        }
      }
    }
  }

  fn alloc_bytes_in(&self, size: u32) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    if size == 0 {
      return Ok(None);
    }
    let header = self.header();
    let mut allocated = header.allocated.load(Ordering::Acquire);

    loop {
      let want = allocated + size;
      if want > self.cap {
        break;
      }

      match header.allocated.compare_exchange_weak(
        allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(offset) => {
          #[cfg(feature = "tracing")]
          tracing::debug!("allocate {} bytes at offset {} from memory", size, offset);

          let allocated = Meta::new(self.ptr as _, offset, size);
          unsafe { allocated.clear(self) };
          return Ok(Some(allocated));
        }
        Err(x) => allocated = x,
      }
    }

    // allocate through slow path
    let mut i = 0;

    loop {
      match self.freelist {
        Freelist::None => {
          return Err(Error::InsufficientSpace {
            requested: size,
            available: self.remaining() as u32,
          })
        }
        Freelist::Optimistic => match self.alloc_slow_path_optimistic(size) {
          Ok(bytes) => return Ok(Some(bytes)),
          Err(e) => {
            if i == self.max_retries - 1 {
              return Err(e);
            }
          }
        },
        Freelist::Pessimistic => match self.alloc_slow_path_pessimistic(size) {
          Ok(bytes) => return Ok(Some(bytes)),
          Err(e) => {
            if i == self.max_retries - 1 {
              return Err(e);
            }
          }
        },
      }

      i += 1;
    }
  }

  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // fn alloc_bytes_within_page_in(&self, size: u32) -> Result<Option<Meta>, Error> {
  //   if self.ro {
  //     return Err(Error::ReadOnly);
  //   }

  //   if size == 0 {
  //     return Ok(None);
  //   }

  //   if size > self.page_size {
  //     return Err(Error::larger_than_page_size(size, self.page_size));
  //   }

  //   let header = self.header();
  //   let mut allocated = header.allocated.load(Ordering::Acquire);
  //   let mut padding_to_next_page = 0;
  //   let want = loop {
  //     let page_boundary = self.nearest_page_boundary(allocated);
  //     let mut want = allocated + size;

  //     // Ensure that the allocation will fit within page
  //     if want > page_boundary {
  //       // Adjust the allocation to start at the next page boundary
  //       padding_to_next_page = page_boundary - allocated;
  //       want += padding_to_next_page;
  //     }

  //     if want > self.cap {
  //       break want;
  //     }

  //     match header.allocated.compare_exchange_weak(
  //       allocated,
  //       want,
  //       Ordering::SeqCst,
  //       Ordering::Acquire,
  //     ) {
  //       Ok(offset) => {
  //         #[cfg(feature = "tracing")]
  //         tracing::debug!(
  //           "allocate {} bytes at offset {} from memory",
  //           size + padding_to_next_page,
  //           offset
  //         );

  //         let mut allocated = Meta::new(self.ptr as _, offset, size + padding_to_next_page);
  //         allocated.ptr_offset = allocated.memory_offset + padding_to_next_page;
  //         allocated.ptr_size = size;
  //         unsafe { allocated.clear(self) };

  //         #[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
  //         self.check_page_boundary(allocated.ptr_offset, allocated.ptr_size);

  //         return Ok(Some(allocated));
  //       }
  //       Err(x) => allocated = x,
  //     }
  //   };

  //   Err(Error::InsufficientSpace {
  //     requested: want - allocated,
  //     available: self.remaining() as u32,
  //   })
  // }

  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[inline]
  // fn nearest_page_boundary(&self, offset: u32) -> u32 {
  //   // Calculate the nearest page boundary after the offset
  //   let remainder = offset % self.page_size;
  //   if remainder == 0 {
  //     offset // Already at a page boundary
  //   } else {
  //     offset + (self.page_size - remainder)
  //   }
  // }

  fn alloc_aligned_bytes_in<T>(&self, extra: u32) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    if mem::size_of::<T>() == 0 {
      return self.alloc_bytes_in(extra);
    }

    let header = self.header();
    let mut allocated = header.allocated.load(Ordering::Acquire);

    let want = loop {
      let aligned_offset = align_offset::<T>(allocated);
      let size = mem::size_of::<T>() as u32;
      let want = aligned_offset + size + extra;
      if want > self.cap {
        break size + extra;
      }

      match header.allocated.compare_exchange_weak(
        allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(offset) => {
          let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
          allocated.align_bytes_to::<T>();
          #[cfg(feature = "tracing")]
          tracing::debug!(
            "allocate {} bytes at offset {} from memory",
            want - offset,
            offset
          );
          return Ok(Some(allocated));
        }
        Err(x) => allocated = x,
      }
    };

    // allocate through slow path
    let mut i = 0;
    loop {
      match self.freelist {
        Freelist::None => {
          return Err(Error::InsufficientSpace {
            requested: want,
            available: self.remaining() as u32,
          })
        }
        Freelist::Optimistic => {
          match self.alloc_slow_path_optimistic(Self::pad::<T>() as u32 + extra) {
            Ok(mut bytes) => {
              bytes.align_bytes_to::<T>();
              return Ok(Some(bytes));
            }
            Err(e) => {
              if i == self.max_retries - 1 {
                return Err(e);
              }
            }
          }
        }
        Freelist::Pessimistic => {
          match self.alloc_slow_path_pessimistic(Self::pad::<T>() as u32 + extra) {
            Ok(mut bytes) => {
              bytes.align_bytes_to::<T>();
              return Ok(Some(bytes));
            }
            Err(e) => {
              if i == self.max_retries - 1 {
                return Err(e);
              }
            }
          }
        }
      }
      i += 1;
    }
  }

  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // fn alloc_aligned_bytes_within_page_in<T>(&self, extra: u32) -> Result<Option<Meta>, Error> {
  //   if self.ro {
  //     return Err(Error::ReadOnly);
  //   }

  //   let t_size = mem::size_of::<T>();

  //   if t_size == 0 {
  //     return self.alloc_bytes_within_page_in(extra);
  //   }

  //   let header = self.header();
  //   let mut allocated = header.allocated.load(Ordering::Acquire);
  //   let want = loop {
  //     let page_boundary = self.nearest_page_boundary(allocated);
  //     let mut aligned_offset = align_offset::<T>(allocated);
  //     let size = t_size as u32;
  //     let mut want = aligned_offset + size + extra;
  //     let mut estimated_size = want - allocated;

  //     // Ensure that the allocation will fit within page
  //     if want > page_boundary {
  //       aligned_offset = align_offset::<T>(page_boundary);
  //       want = aligned_offset + size + extra;
  //       estimated_size = (aligned_offset - page_boundary) + size + extra;
  //     }

  //     if estimated_size > self.page_size {
  //       return Err(Error::larger_than_page_size(estimated_size, self.page_size));
  //     }

  //     if want > self.cap {
  //       break want;
  //     }

  //     match header.allocated.compare_exchange_weak(
  //       allocated,
  //       want,
  //       Ordering::SeqCst,
  //       Ordering::Acquire,
  //     ) {
  //       Ok(offset) => {
  //         let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
  //         allocated.ptr_offset = aligned_offset;
  //         allocated.ptr_size = size + extra;
  //         unsafe { allocated.clear(self) };

  //         #[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
  //         self.check_page_boundary(allocated.ptr_offset, allocated.ptr_size);

  //         #[cfg(feature = "tracing")]
  //         tracing::debug!(
  //           "allocate {} bytes at offset {} from memory",
  //           want - offset,
  //           offset
  //         );
  //         return Ok(Some(allocated));
  //       }
  //       Err(x) => allocated = x,
  //     }
  //   };

  //   Err(Error::InsufficientSpace {
  //     requested: want,
  //     available: self.remaining() as u32,
  //   })
  // }

  fn alloc_in<T>(&self) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let t_size = mem::size_of::<T>();
    if t_size == 0 {
      return Ok(None);
    }

    let header = self.header();
    let mut allocated = header.allocated.load(Ordering::Acquire);
    let want = loop {
      let align_offset = align_offset::<T>(allocated);
      let size = t_size as u32;
      let want = align_offset + size;
      if want > self.cap {
        break size;
      }

      match header.allocated.compare_exchange_weak(
        allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(offset) => {
          let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
          allocated.align_to::<T>();

          #[cfg(feature = "tracing")]
          tracing::debug!(
            "allocate {} bytes at offset {} from memory",
            want - offset,
            offset
          );

          unsafe { allocated.clear(self) };
          return Ok(Some(allocated));
        }
        Err(x) => allocated = x,
      }
    };

    // allocate through slow path
    let mut i = 0;

    loop {
      match self.freelist {
        Freelist::None => {
          return Err(Error::InsufficientSpace {
            requested: want,
            available: self.remaining() as u32,
          })
        }
        Freelist::Optimistic => match self.alloc_slow_path_optimistic(Self::pad::<T>() as u32) {
          Ok(mut allocated) => {
            allocated.align_to::<T>();
            return Ok(Some(allocated));
          }
          Err(e) => {
            if i == self.max_retries - 1 {
              return Err(e);
            }
          }
        },
        Freelist::Pessimistic => match self.alloc_slow_path_pessimistic(Self::pad::<T>() as u32) {
          Ok(mut allocated) => {
            allocated.align_to::<T>();
            return Ok(Some(allocated));
          }
          Err(e) => {
            if i == self.max_retries - 1 {
              return Err(e);
            }
          }
        },
      }

      i += 1;
    }
  }

  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // fn alloc_within_page_in<T>(&self) -> Result<Option<Meta>, Error> {
  //   if self.ro {
  //     return Err(Error::ReadOnly);
  //   }

  //   let t_size = mem::size_of::<T>();

  //   if t_size == 0 {
  //     return Ok(None);
  //   }

  //   if t_size as u32 > self.page_size {
  //     return Err(Error::larger_than_page_size(t_size as u32, self.page_size));
  //   }

  //   let header = self.header();
  //   let mut allocated = header.allocated.load(Ordering::Acquire);
  //   let want = loop {
  //     let page_boundary = self.nearest_page_boundary(allocated);
  //     let mut aligned_offset = align_offset::<T>(allocated);
  //     let size = mem::size_of::<T>() as u32;
  //     let mut want = aligned_offset + size;
  //     let mut estimated_size = want - allocated;

  //     // Ensure that the allocation will fit within page
  //     if want > page_boundary {
  //       aligned_offset = align_offset::<T>(page_boundary);
  //       want = aligned_offset + size;
  //       estimated_size = (aligned_offset - page_boundary) + size;
  //     }

  //     if estimated_size > self.page_size {
  //       return Err(Error::larger_than_page_size(estimated_size, self.page_size));
  //     }

  //     if want > self.cap {
  //       break want;
  //     }

  //     match header.allocated.compare_exchange_weak(
  //       allocated,
  //       want,
  //       Ordering::SeqCst,
  //       Ordering::Acquire,
  //     ) {
  //       Ok(offset) => {
  //         let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
  //         allocated.ptr_offset = aligned_offset;
  //         allocated.ptr_size = size;
  //         unsafe { allocated.clear(self) };

  //         #[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
  //         self.check_page_boundary(allocated.ptr_offset, allocated.ptr_size);

  //         #[cfg(feature = "tracing")]
  //         tracing::debug!(
  //           "allocate {} bytes at offset {} from memory",
  //           want - offset,
  //           offset
  //         );

  //         unsafe { allocated.clear(self) };
  //         return Ok(Some(allocated));
  //       }
  //       Err(x) => allocated = x,
  //     }
  //   };

  //   Err(Error::InsufficientSpace {
  //     requested: want,
  //     available: self.remaining() as u32,
  //   })
  // }

  fn alloc_slow_path_pessimistic(&self, size: u32) -> Result<Meta, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let backoff = Backoff::new();

    loop {
      let Some(((prev_node_val, prev_node), (next_node_val, next_node))) =
        self.find_prev_and_next(size, |val, next_node_size| val <= next_node_size)
      else {
        return Err(Error::InsufficientSpace {
          requested: size,
          available: self.remaining() as u32,
        });
      };

      let (prev_node_size, next_node_offset) = decode_segment_node(prev_node_val);
      if prev_node_size == REMOVED_SEGMENT_NODE {
        // the current node is marked as removed, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      let (next_node_size, next_next_node_offset) = decode_segment_node(next_node_val);
      if next_node_size == REMOVED_SEGMENT_NODE {
        // the current node is marked as removed, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // mark next node as removed
      let removed_next = encode_segment_node(REMOVED_SEGMENT_NODE, next_next_node_offset);
      if next_node
        .compare_exchange(
          next_node_val,
          removed_next,
          Ordering::AcqRel,
          Ordering::Relaxed,
        )
        .is_err()
      {
        // wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      let remaining = next_node_size - size;

      let segment_node = unsafe { Segment::from_offset(self, next_node_offset, next_node_size) };

      // update the prev node to point to the next next node.
      let updated_prev = encode_segment_node(prev_node_size, next_next_node_offset);
      match prev_node.compare_exchange(
        prev_node_val,
        updated_prev,
        Ordering::AcqRel,
        Ordering::Relaxed,
      ) {
        Ok(_) => {
          #[cfg(feature = "tracing")]
          tracing::debug!(
            "allocate {} bytes at offset {} from segment",
            size,
            next_node_offset
          );

          let mut memory_size = next_node_size;
          let data_end_offset = segment_node.data_offset + size;
          // check if the remaining is enough to allocate a new segment.
          if self.validate_segment(data_end_offset, remaining) {
            memory_size -= remaining;
            // We have successfully remove the head node from the list.
            // Then we can allocate the memory.
            // give back the remaining memory to the free list.

            // Safety: the `next + size` is in bounds, and `node_size - size` is also in bounds.
            self.pessimistic_dealloc(data_end_offset, remaining);
          }

          let mut allocated = Meta::new(self.ptr as _, segment_node.ptr_offset, memory_size);
          allocated.ptr_offset = segment_node.data_offset;
          allocated.ptr_size = size;
          unsafe {
            allocated.clear(self);
          }
          return Ok(allocated);
        }
        Err(current) => {
          let (node_size, _) = decode_segment_node(current);
          if node_size == REMOVED_SEGMENT_NODE {
            // the current node is marked as removed, wait other thread to make progress.
            backoff.snooze();
          } else {
            backoff.spin();
          }
        }
      }
    }
  }

  /// It is like a pop operation, we will always allocate from the largest segment.
  fn alloc_slow_path_optimistic(&self, size: u32) -> Result<Meta, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let backoff = Backoff::new();
    let header = self.header();

    loop {
      let sentinel = header.sentinel.load(Ordering::Acquire);
      let (sentinel_node_size, head_node_offset) = decode_segment_node(sentinel);

      // free list is empty
      if sentinel_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && head_node_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return Err(Error::InsufficientSpace {
          requested: size,
          available: self.remaining() as u32,
        });
      }

      if head_node_offset == REMOVED_SEGMENT_NODE {
        // the head node is marked as removed, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      let head = self.get_segment_node(head_node_offset);
      let head_node_size_and_next_node_offset = head.load(Ordering::Acquire);
      let (head_node_size, next_node_offset) =
        decode_segment_node(head_node_size_and_next_node_offset);

      if head_node_size == REMOVED_SEGMENT_NODE {
        // the head node is marked as removed, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // The larget segment does not have enough space to allocate, so just return err.
      if size > head_node_size {
        return Err(Error::InsufficientSpace {
          requested: size,
          available: head_node_size,
        });
      }

      let remaining = head_node_size - size;

      // Safety: the `next` and `node_size` are valid, because they just come from the sentinel.
      let segment_node = unsafe { Segment::from_offset(self, head_node_offset, head_node_size) };

      if head_node_size == REMOVED_SEGMENT_NODE {
        // the head node is marked as removed, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // CAS to remove the current head
      let removed_head = encode_segment_node(REMOVED_SEGMENT_NODE, next_node_offset);
      if head
        .compare_exchange(
          head_node_size_and_next_node_offset,
          removed_head,
          Ordering::AcqRel,
          Ordering::Relaxed,
        )
        .is_err()
      {
        // wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // We have successfully mark the head is removed, then we need to let sentinel node points to the next node.
      match header.sentinel.compare_exchange(
        sentinel,
        encode_segment_node(sentinel_node_size, next_node_offset),
        Ordering::AcqRel,
        Ordering::Relaxed,
      ) {
        Ok(_) => {
          #[cfg(feature = "tracing")]
          tracing::debug!(
            "allocate {} bytes at offset {} from segment",
            size,
            segment_node.data_offset
          );

          let mut memory_size = head_node_size;
          let data_end_offset = segment_node.data_offset + size;
          // check if the remaining is enough to allocate a new segment.
          if self.validate_segment(data_end_offset, remaining) {
            memory_size -= remaining;
            // We have successfully remove the head node from the list.
            // Then we can allocate the memory.
            // give back the remaining memory to the free list.

            // Safety: the `next + size` is in bounds, and `node_size - size` is also in bounds.
            self.optimistic_dealloc(data_end_offset, remaining);
          }

          let mut allocated = Meta::new(self.ptr as _, segment_node.ptr_offset, memory_size);
          allocated.ptr_offset = segment_node.data_offset;
          allocated.ptr_size = size;
          unsafe {
            allocated.clear(self);
          }
          return Ok(allocated);
        }
        Err(current) => {
          let (node_size, _) = decode_segment_node(current);
          if node_size == REMOVED_SEGMENT_NODE {
            // The current head is removed from the list, wait other thread to make progress.
            backoff.snooze();
          } else {
            backoff.spin();
          }
        }
      }
    }
  }

  fn discard_freelist_in(&self) -> u32 {
    let backoff = Backoff::new();
    let header = self.header();
    let mut discarded = 0;
    loop {
      let sentinel = header.sentinel.load(Ordering::Acquire);
      let (sentinel_node_size, head_node_offset) = decode_segment_node(sentinel);

      // free list is empty
      if sentinel_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && head_node_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return discarded;
      }

      if head_node_offset == REMOVED_SEGMENT_NODE {
        // the head node is marked as removed, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      let head = self.get_segment_node(head_node_offset);
      let head_node_size_and_next_node_offset = head.load(Ordering::Acquire);
      let (head_node_size, next_node_offset) =
        decode_segment_node(head_node_size_and_next_node_offset);

      if head_node_size == REMOVED_SEGMENT_NODE {
        // the head node is marked as removed, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // Safety: the `next` and `node_size` are valid, because they just come from the sentinel.
      let segment_node = unsafe { Segment::from_offset(self, head_node_offset, head_node_size) };

      if head_node_size == REMOVED_SEGMENT_NODE {
        // the head node is marked as removed, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // CAS to remove the current head
      let removed_head = encode_segment_node(REMOVED_SEGMENT_NODE, next_node_offset);
      if head
        .compare_exchange(
          head_node_size_and_next_node_offset,
          removed_head,
          Ordering::AcqRel,
          Ordering::Relaxed,
        )
        .is_err()
      {
        // wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // We have successfully mark the head is removed, then we need to let sentinel node points to the next node.
      match header.sentinel.compare_exchange(
        sentinel,
        encode_segment_node(sentinel_node_size, next_node_offset),
        Ordering::AcqRel,
        Ordering::Relaxed,
      ) {
        Ok(_) => {
          // incresase the discarded memory.
          self.increase_discarded(segment_node.data_size);
          discarded += segment_node.data_size;
          continue;
        }
        Err(current) => {
          let (node_size, _) = decode_segment_node(current);
          if node_size == REMOVED_SEGMENT_NODE {
            // The current head is removed from the list, wait other thread to make progress.
            backoff.snooze();
          } else {
            backoff.spin();
          }
        }
      }
    }
  }

  /// Returns `true` if this offset and size is valid for a segment node.
  #[inline]
  fn validate_segment(&self, offset: u32, size: u32) -> bool {
    if offset == 0 || size == 0 {
      return false;
    }

    let aligned_offset = align_offset::<AtomicU64>(offset) as usize;
    let padding = aligned_offset - offset as usize;
    let segmented_node_size = padding + SEGMENT_NODE_SIZE;
    if segmented_node_size >= size as usize {
      return false;
    }

    let available_bytes = size - segmented_node_size as u32;
    if available_bytes < self.header().min_segment_size.load(Ordering::Acquire) {
      return false;
    }

    true
  }

  #[inline]
  fn try_new_segment(&self, offset: u32, size: u32) -> Option<Segment> {
    if offset == 0 || size == 0 {
      return None;
    }

    let aligned_offset = align_offset::<AtomicU64>(offset) as usize;
    let padding = aligned_offset - offset as usize;
    let segmented_node_size = padding + SEGMENT_NODE_SIZE;
    if segmented_node_size >= size as usize {
      self.increase_discarded(size);
      return None;
    }

    let available_bytes = size - segmented_node_size as u32;
    if available_bytes < self.header().min_segment_size.load(Ordering::Acquire) {
      self.increase_discarded(size);
      return None;
    }

    Some(Segment {
      ptr: self.ptr,
      ptr_offset: aligned_offset as u32,
      data_offset: (aligned_offset + SEGMENT_NODE_SIZE) as u32,
      data_size: available_bytes,
    })
  }

  #[inline]
  fn get_segment_node(&self, offset: u32) -> &AtomicU64 {
    // Safety: the offset is in bounds and well aligned.
    unsafe {
      let ptr = self.ptr.add(offset as usize);
      &*(ptr as *const _)
    }
  }

  #[inline]
  fn pad<T>() -> usize {
    let size = mem::size_of::<T>();
    let align = mem::align_of::<T>();
    size + align - 1
  }

  // #[cfg(test)]
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[inline]
  // fn check_page_boundary(&self, offset: u32, len: u32) {
  //   if len == 0 {
  //     return; // A zero-length range is trivially within the same "page"
  //   }

  //   // Calculate the page boundary of the start and end of the range
  //   let start_page = offset / self.page_size;
  //   let end_page = (offset + len - 1) / self.page_size;

  //   assert_eq!(
  //     start_page, end_page,
  //     "start and end of range must be in the same page"
  //   );
  // }

  #[cfg(test)]
  #[cfg(feature = "std")]
  #[allow(dead_code)]
  pub(super) fn print_segment_list(&self) {
    let header = self.header();
    let mut current: &AtomicU64 = &header.sentinel;

    loop {
      let current_node = current.load(Ordering::Acquire);
      let (node_size, next_node_offset) = decode_segment_node(current_node);

      if node_size == SENTINEL_SEGMENT_NODE_SIZE {
        if next_node_offset == SENTINEL_SEGMENT_NODE_OFFSET {
          break;
        }

        current = self.get_segment_node(next_node_offset);
        continue;
      }

      std::println!("node_size: {node_size}, next_node_offset: {next_node_offset}",);

      if next_node_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        break;
      }
      current = self.get_segment_node(next_node_offset);
    }
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    unsafe {
      let memory_ptr = self.inner.as_ptr();
      let memory = &*memory_ptr;
      // `Memory` storage... follow the drop steps from Arc.
      if memory.refs().fetch_sub(1, Ordering::Release) != 1 {
        return;
      }

      // This fence is needed to prevent reordering of use of the data and
      // deletion of the data.  Because it is marked `Release`, the decreasing
      // of the reference count synchronizes with this `Acquire` fence. This
      // means that use of the data happens before decreasing the reference
      // count, which happens before this fence, which happens before the
      // deletion of the data.
      //
      // As explained in the [Boost documentation][1],
      //
      // > It is important to enforce any possible access to the object in one
      // > thread (through an existing reference) to *happen before* deleting
      // > the object in a different thread. This is achieved by a "release"
      // > operation after dropping a reference (any access to the object
      // > through this reference must obviously happened before), and an
      // > "acquire" operation before deleting the object.
      //
      // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
      //
      // Thread sanitizer does not support atomic fences. Use an atomic load
      // instead.
      memory.refs().load(Ordering::Acquire);
      // Drop the data
      let mut memory = Box::from_raw(memory_ptr);

      // Relaxed is enough here as we're in a drop, no one else can
      // access this memory anymore.
      memory.unmount();
    }
  }
}

#[cfg(test)]
mod tests;
