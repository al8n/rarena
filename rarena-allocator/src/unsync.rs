use core::{
  fmt,
  mem::{self, MaybeUninit},
  ptr::{self, NonNull},
  slice,
};

use super::{common::*, sealed::Sealed, *};

#[allow(unused_imports)]
use std::boxed::Box;

#[cfg(feature = "std")]
type Memory =
  super::memory::Memory<UnsafeCell<usize>, std::rc::Rc<std::path::PathBuf>, sealed::Header>;

#[cfg(not(feature = "std"))]
type Memory = super::memory::Memory<UnsafeCell<usize>, std::rc::Rc<()>, sealed::Header>;

const SEGMENT_NODE_SIZE: usize = mem::size_of::<SegmentNode>();

mod sealed {
  use super::*;

  #[derive(Debug)]
  #[repr(C, align(8))]
  pub struct Header {
    /// The sentinel node for the ordered free list.
    pub(super) sentinel: SegmentNode,
    pub(super) allocated: u32,
    pub(super) min_segment_size: u32,
    pub(super) discarded: u32,
  }

  impl super::super::sealed::Header for Header {
    #[inline]
    fn new(size: u32, min_segment_size: u32) -> Self {
      Self {
        allocated: size,
        sentinel: SegmentNode::sentinel(),
        min_segment_size,
        discarded: 0,
      }
    }

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[inline]
    fn load_allocated(&self) -> u32 {
      self.allocated
    }

    #[inline]
    fn load_min_segment_size(&self) -> u32 {
      self.min_segment_size
    }
  }
}

#[repr(transparent)]
struct SegmentNode(
  /// The first 32 bits are the size of the memory,
  /// the last 32 bits are the offset of the next segment node.
  UnsafeCell<u64>,
);

impl core::fmt::Debug for SegmentNode {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (offset, next) = decode_segment_node(*self.0.as_inner_ref());
    f.debug_struct("SegmentNode")
      .field("offset", &offset)
      .field("next", &next)
      .finish()
  }
}

impl core::ops::Deref for SegmentNode {
  type Target = UnsafeCell<u64>;

  #[inline]
  fn deref(&self) -> &Self::Target {
    &self.0
  }
}

impl SegmentNode {
  #[inline]
  fn sentinel() -> Self {
    Self(UnsafeCell::new(encode_segment_node(
      SENTINEL_SEGMENT_NODE_OFFSET,
      SENTINEL_SEGMENT_NODE_OFFSET,
    )))
  }

  #[allow(clippy::mut_from_ref)]
  #[inline]
  fn as_inner_mut(&self) -> &mut u64 {
    unsafe { &mut *self.0.as_inner_mut() }
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
  /// - offset must be a well-aligned and in-bounds `u64` pointer.
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
  fn as_mut(&mut self) -> &mut SegmentNode {
    // Safety: when constructing the Segment, we have checked the ptr_offset is in bounds and well-aligned.
    unsafe {
      let ptr = self.ptr.add(self.ptr_offset as usize);
      &mut *ptr.cast::<SegmentNode>()
    }
  }

  #[inline]
  fn update_next_node(&mut self, next: u32) {
    *self.as_mut().as_inner_mut() = encode_segment_node(self.data_size, next);
  }
}

/// Arena should be lock-free
pub struct Arena {
  ptr: *mut u8,
  cap: u32,
  inner: NonNull<Memory>,

  // Once constructed, the below fields are immutable
  reserved: usize,
  data_offset: u32,
  flag: MemoryFlags,
  max_retries: u8,
  unify: bool,
  magic_version: u16,
  version: u16,
  ro: bool,
  freelist: Freelist,
  page_size: u32,
}

impl fmt::Debug for Arena {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let header = self.header();
    let allocated = header.allocated;

    f.debug_struct("Arena")
      .field("cap", &self.cap)
      .field("data_offset", &self.data_offset)
      .field("allocated", &allocated)
      .field("discarded", &header.discarded)
      .field("freelist", &self.freelist)
      .field("page_size", &self.page_size)
      .field("reserved", &self.reserved)
      .field("magic_version", &self.magic_version)
      .field("version", &self.version)
      .field("read_only", &self.ro)
      .field("unify", &self.unify)
      .finish()
  }
}

impl Clone for Arena {
  fn clone(&self) -> Self {
    unsafe {
      use super::sealed::RefCounter;

      let memory = self.inner.as_ref();

      let old_size = memory.refs().fetch_add(1, Ordering::Release);
      if old_size > usize::MAX >> 1 {
        dbutils::abort();
      }

      // Safety:
      // The ptr is always non-null, and the data is only deallocated when the
      // last Arena is dropped.
      Self {
        max_retries: self.max_retries,
        reserved: self.reserved,
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
      reserved: memory.reserved(),
      freelist: memory.freelist(),
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
  #[cfg(feature = "std")]
  type PathRefCounter = std::rc::Rc<std::path::PathBuf>;

  #[cfg(not(feature = "std"))]
  type PathRefCounter = std::rc::Rc<()>;

  type RefCounter = UnsafeCell<usize>;

  type Header = sealed::Header;
}

impl AsRef<Memory> for Arena {
  #[inline]
  fn as_ref(&self) -> &Memory {
    // Safety: the inner is always non-null.
    unsafe { self.inner.as_ref() }
  }
}

impl Allocator for Arena {
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  type Path = std::rc::Rc<std::path::PathBuf>;

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
    self.header().allocated as usize
  }

  #[inline]
  fn raw_mut_ptr(&self) -> *mut u8 {
    self.ptr
  }

  #[inline]
  fn raw_ptr(&self) -> *const u8 {
    self.ptr
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
    let header = self.header_mut();
    // if the offset + size is the current allocated size, then we can deallocate the memory back to the main memory.
    if header.allocated == offset + size {
      header.allocated = offset;
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
    self.header().discarded
  }

  #[inline]
  fn increase_discarded(&self, size: u32) {
    #[cfg(feature = "tracing")]
    tracing::debug!("discard {size} bytes");

    self.header_mut().discarded += size;
  }

  #[inline]
  fn magic_version(&self) -> u16 {
    self.magic_version
  }

  #[inline]
  fn minimum_segment_size(&self) -> u32 {
    self.header().min_segment_size
  }

  #[inline]
  fn set_minimum_segment_size(&self, size: u32) {
    self.header_mut().min_segment_size = size;
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn path(&self) -> Option<&Self::Path> {
    // Safety: the inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { self.inner.as_ref().path() }
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
  fn refs(&self) -> usize {
    unsafe { *self.inner.as_ref().refs().as_inner_ref() }
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
    unsafe { (*self.inner.as_ptr()).set_remove_on_drop(remove_on_drop) }
  }

  unsafe fn rewind(&self, pos: ArenaPosition) {
    let data_offset = self.data_offset;
    let cap = self.cap;
    let header = self.header_mut();
    let allocated = header.allocated;
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

    header.allocated = final_offset;
  }

  #[inline]
  fn version(&self) -> u16 {
    self.version
  }
}

impl Arena {
  /// Truncate the ARENA to a new capacity.
  ///
  /// **Note:** If the new capacity is less than the current allocated size, then the ARENA will be truncated to the allocated size.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub fn truncate(&mut self, mut size: usize) -> std::io::Result<()> {
    if self.ro {
      return Err(std::io::Error::new(
        std::io::ErrorKind::PermissionDenied,
        "ARENA is read-only",
      ));
    }

    let allocated = self.allocated();
    if allocated >= size {
      size = allocated;
    }

    unsafe {
      let memory = self.inner.as_mut();
      memory.truncate(allocated, size)?;
      self.ptr = memory.as_mut_ptr();
      self.cap = memory.cap();
    }
    Ok(())
  }

  /// Truncate the ARENA to a new capacity.
  ///
  /// **Note:** If the new capacity is less than the current allocated size, then the ARENA will be truncated to the allocated size.
  #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
  pub fn truncate(&mut self, mut size: usize) {
    let allocated = self.allocated();
    if allocated >= size {
      size = allocated;
    }

    unsafe {
      let memory = self.inner.as_mut();
      memory.truncate(allocated, size);
      self.ptr = memory.as_mut_ptr();
      self.cap = memory.cap();
    }
  }

  #[inline]
  fn header(&self) -> &sealed::Header {
    // Safety:
    // The inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { (*self.inner.as_ptr()).header() }
  }

  #[allow(clippy::mut_from_ref)]
  #[inline]
  fn header_mut(&self) -> &mut sealed::Header {
    // Safety:
    // The inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { (*self.inner.as_ptr()).header_mut() }
  }

  /// Returns the free list position to insert the value.
  /// - `None` means that we should insert to the head.
  /// - `Some(offset)` means that we should insert after the offset. offset -> new -> next
  fn find_position(&self, val: u32, check: impl Fn(u32, u32) -> bool) -> (u64, &UnsafeCell<u64>) {
    let header = self.header_mut();
    let mut current: &UnsafeCell<u64> = &header.sentinel;
    let mut current_node = current.as_inner_ref();
    let (mut current_node_size, mut next_offset) = decode_segment_node(*current_node);

    loop {
      // the list is empty
      if current_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && next_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return (*current_node, current);
      }

      // the current is marked as remove and the next is the tail.
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return (*current_node, current);
      }

      // the next is the tail, then we should insert the value after the current node.
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return (*current_node, current);
      }

      let next = self.get_segment_node(next_offset);
      let next_node = next.as_inner_ref();
      let (next_node_size, next_next_offset) = decode_segment_node(*next_node);

      if check(val, next_node_size) {
        return (*current_node, current);
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
  ) -> Option<((u64, &UnsafeCell<u64>), (u64, &UnsafeCell<u64>))> {
    let header = self.header();
    let mut current: &UnsafeCell<u64> = &header.sentinel;
    let mut current_node = current.as_inner_ref();
    let (mut current_node_size, mut next_offset) = decode_segment_node(*current_node);

    loop {
      // the list is empty
      if current_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && next_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return None;
      }

      // the current is marked as remove and the next is the tail.
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return None;
      }

      // the next is the tail
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return None;
      }

      let next = self.get_segment_node(next_offset);
      let next_node = next.as_inner_ref();
      let (next_node_size, next_next_offset) = decode_segment_node(*next_node);

      if check(val, next_node_size) {
        return Some(((*current_node, current), (*next_node, next)));
      }

      current = self.get_segment_node(next_offset);
      current_node = next_node;
      current_node_size = next_node_size;
      next_offset = next_next_offset;
    }
  }

  fn optimistic_dealloc(&self, offset: u32, size: u32) -> bool {
    // check if we have enough space to allocate a new segment in this segment.
    let Some(mut segment_node) = self.try_new_segment(offset, size) else {
      return false;
    };

    loop {
      let (current_node_size_and_next_node_offset, current) = self
        .find_position(segment_node.data_size, |val, next_node_size| {
          val >= next_node_size
        });
      let (node_size, next_node_offset) =
        decode_segment_node(current_node_size_and_next_node_offset);

      if segment_node.ptr_offset == next_node_offset {
        continue;
      }

      segment_node.update_next_node(next_node_offset);

      *current.as_inner_ref_mut() = encode_segment_node(node_size, segment_node.ptr_offset);

      #[cfg(feature = "tracing")]
      tracing::debug!(
        "create segment node ({} bytes) at {}, next segment {next_node_offset}",
        segment_node.data_size,
        segment_node.ptr_offset
      );

      self.increase_discarded(segment_node.data_offset - segment_node.ptr_offset);
      return true;
    }
  }

  fn pessimistic_dealloc(&self, offset: u32, size: u32) -> bool {
    // check if we have enough space to allocate a new segment in this segment.
    let Some(mut segment_node) = self.try_new_segment(offset, size) else {
      return false;
    };

    let (current_node_size_and_next_node_offset, current) = self
      .find_position(segment_node.data_size, |val, next_node_size| {
        val <= next_node_size
      });
    let (node_size, next_node_offset) = decode_segment_node(current_node_size_and_next_node_offset);

    segment_node.update_next_node(next_node_offset);

    *current.as_inner_ref_mut() = encode_segment_node(node_size, segment_node.ptr_offset);

    #[cfg(feature = "tracing")]
    tracing::debug!(
      "create segment node ({} bytes) at {}, next segment {next_node_offset}",
      segment_node.data_size,
      segment_node.ptr_offset
    );

    self.increase_discarded(segment_node.data_offset - segment_node.ptr_offset);
    true
  }

  fn alloc_bytes_in(&self, size: u32) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    if size == 0 {
      return Ok(None);
    }
    let header = self.header_mut();

    let want = header.allocated + size;
    if want <= self.cap {
      let offset = header.allocated;
      header.allocated = want;

      #[cfg(feature = "tracing")]
      tracing::debug!("allocate {} bytes at offset {} from memory", size, offset);

      let allocated = Meta::new(self.ptr as _, offset, size);
      unsafe { allocated.clear(self) };
      return Ok(Some(allocated));
    }

    // allocate through slow path
    match self.freelist {
      Freelist::None => Err(Error::InsufficientSpace {
        requested: size,
        available: self.remaining() as u32,
      }),
      Freelist::Optimistic => match self.alloc_slow_path_optimistic(size) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(e) => Err(e),
      },
      Freelist::Pessimistic => match self.alloc_slow_path_pessimistic(size) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(e) => Err(e),
      },
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

  //   let header = self.header_mut();
  //   let mut padding_to_next_page = 0;

  //   let page_boundary = self.nearest_page_boundary(header.allocated);
  //   let mut want = header.allocated + size;

  //   // Ensure that the allocation will fit within page
  //   if want > page_boundary {
  //     // Adjust the allocation to start at the next page boundary
  //     padding_to_next_page = page_boundary - header.allocated;
  //     want += padding_to_next_page;
  //   }

  //   if want <= self.cap {
  //     let offset = header.allocated;
  //     header.allocated = want;

  //     #[cfg(feature = "tracing")]
  //     tracing::debug!(
  //       "allocate {} bytes at offset {} from memory",
  //       size + padding_to_next_page,
  //       offset
  //     );

  //     let mut allocated = Meta::new(self.ptr as _, offset, size + padding_to_next_page);
  //     allocated.ptr_offset = allocated.memory_offset + padding_to_next_page;
  //     allocated.ptr_size = size;
  //     unsafe { allocated.clear(self) };

  //     #[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
  //     self.check_page_boundary(allocated.ptr_offset, allocated.ptr_size);

  //     return Ok(Some(allocated));
  //   }

  //   Err(Error::InsufficientSpace {
  //     requested: want - header.allocated,
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

    let header = self.header_mut();
    let allocated = header.allocated;
    let aligned_offset = align_offset::<T>(allocated);
    let size = mem::size_of::<T>() as u32;
    let want = aligned_offset + size + extra;

    if want <= self.cap {
      // break size + extra;
      let offset = header.allocated;
      header.allocated = want;
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

    // allocate through slow path
    match self.freelist {
      Freelist::None => Err(Error::InsufficientSpace {
        requested: size + extra,
        available: self.remaining() as u32,
      }),
      Freelist::Optimistic => {
        match self.alloc_slow_path_optimistic(Self::pad::<T>() as u32 + extra) {
          Ok(mut bytes) => {
            bytes.align_bytes_to::<T>();
            Ok(Some(bytes))
          }
          Err(e) => Err(e),
        }
      }
      Freelist::Pessimistic => {
        match self.alloc_slow_path_pessimistic(Self::pad::<T>() as u32 + extra) {
          Ok(mut bytes) => {
            bytes.align_bytes_to::<T>();
            Ok(Some(bytes))
          }
          Err(e) => Err(e),
        }
      }
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

  //   let header = self.header_mut();
  //   let allocated = header.allocated;

  //   let page_boundary = self.nearest_page_boundary(allocated);
  //   let mut aligned_offset = align_offset::<T>(allocated);
  //   let size = t_size as u32;
  //   let mut want = aligned_offset + size + extra;
  //   let mut estimated_size = want - allocated;

  //   // Ensure that the allocation will fit within page
  //   if want > page_boundary {
  //     aligned_offset = align_offset::<T>(page_boundary);
  //     want = aligned_offset + size + extra;
  //     estimated_size = (aligned_offset - page_boundary) + size + extra;
  //   }

  //   if estimated_size > self.page_size {
  //     return Err(Error::larger_than_page_size(estimated_size, self.page_size));
  //   }

  //   if want <= self.cap {
  //     let offset = header.allocated;
  //     header.allocated = want;

  //     let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
  //     allocated.ptr_offset = aligned_offset;
  //     allocated.ptr_size = size + extra;
  //     unsafe { allocated.clear(self) };

  //     #[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
  //     self.check_page_boundary(allocated.ptr_offset, allocated.ptr_size);

  //     #[cfg(feature = "tracing")]
  //     tracing::debug!(
  //       "allocate {} bytes at offset {} from memory",
  //       want - offset,
  //       offset
  //     );
  //     return Ok(Some(allocated));
  //   }

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

    let header = self.header_mut();
    let allocated = header.allocated;
    let align_offset = align_offset::<T>(allocated);
    let size = t_size as u32;
    let want = align_offset + size;

    if want <= self.cap {
      let offset = header.allocated;
      header.allocated = want;
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

    // allocate through slow path
    match self.freelist {
      Freelist::None => Err(Error::InsufficientSpace {
        requested: want,
        available: self.remaining() as u32,
      }),
      Freelist::Optimistic => match self.alloc_slow_path_optimistic(Self::pad::<T>() as u32) {
        Ok(mut allocated) => {
          allocated.align_to::<T>();
          Ok(Some(allocated))
        }
        Err(e) => Err(e),
      },
      Freelist::Pessimistic => match self.alloc_slow_path_pessimistic(Self::pad::<T>() as u32) {
        Ok(mut allocated) => {
          allocated.align_to::<T>();
          Ok(Some(allocated))
        }
        Err(e) => Err(e),
      },
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

  //   let header = self.header_mut();
  //   let allocated = header.allocated;
  //   let page_boundary = self.nearest_page_boundary(allocated);
  //   let mut aligned_offset = align_offset::<T>(allocated);
  //   let size = mem::size_of::<T>() as u32;
  //   let mut want = aligned_offset + size;
  //   let mut estimated_size = want - allocated;

  //   // Ensure that the allocation will fit within page
  //   if want > page_boundary {
  //     aligned_offset = align_offset::<T>(page_boundary);
  //     want = aligned_offset + size;
  //     estimated_size = (aligned_offset - page_boundary) + size;
  //   }

  //   if estimated_size > self.page_size {
  //     return Err(Error::larger_than_page_size(estimated_size, self.page_size));
  //   }

  //   if want <= self.cap {
  //     let offset = header.allocated;
  //     header.allocated = want;
  //     let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
  //     allocated.ptr_offset = aligned_offset;
  //     allocated.ptr_size = size;
  //     unsafe { allocated.clear(self) };

  //     #[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
  //     self.check_page_boundary(allocated.ptr_offset, allocated.ptr_size);

  //     #[cfg(feature = "tracing")]
  //     tracing::debug!(
  //       "allocate {} bytes at offset {} from memory",
  //       want - offset,
  //       offset
  //     );

  //     unsafe { allocated.clear(self) };
  //     return Ok(Some(allocated));
  //   }

  //   Err(Error::InsufficientSpace {
  //     requested: want,
  //     available: self.remaining() as u32,
  //   })
  // }

  fn alloc_slow_path_pessimistic(&self, size: u32) -> Result<Meta, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let Some(((prev_node_val, prev_node), (next_node_val, _))) =
      self.find_prev_and_next(size, |val, next_node_size| val <= next_node_size)
    else {
      return Err(Error::InsufficientSpace {
        requested: size,
        available: self.remaining() as u32,
      });
    };

    let (prev_node_size, next_node_offset) = decode_segment_node(prev_node_val);
    let (next_node_size, next_next_node_offset) = decode_segment_node(next_node_val);

    let remaining = next_node_size - size;

    let segment_node = unsafe { Segment::from_offset(self, next_node_offset, next_node_size) };

    // update the prev node to point to the next next node.
    let updated_prev = encode_segment_node(prev_node_size, next_next_node_offset);

    *prev_node.as_inner_ref_mut() = updated_prev;

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
    Ok(allocated)
  }

  /// It is like a pop operation, we will always allocate from the largest segment.
  fn alloc_slow_path_optimistic(&self, size: u32) -> Result<Meta, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let header = self.header();

    let sentinel = header.sentinel.as_inner_ref();
    let (sentinel_node_size, head_node_offset) = decode_segment_node(*sentinel);

    // free list is empty
    if sentinel_node_size == SENTINEL_SEGMENT_NODE_SIZE
      && head_node_offset == SENTINEL_SEGMENT_NODE_OFFSET
    {
      return Err(Error::InsufficientSpace {
        requested: size,
        available: self.remaining() as u32,
      });
    }

    let head = self.get_segment_node(head_node_offset);
    let head_node_size_and_next_node_offset = head.as_inner_ref();
    let (head_node_size, next_node_offset) =
      decode_segment_node(*head_node_size_and_next_node_offset);

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

    *header.sentinel.as_inner_mut() = encode_segment_node(sentinel_node_size, next_node_offset);

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
    Ok(allocated)
  }

  fn discard_freelist_in(&self) -> u32 {
    let header = self.header();
    let mut discarded = 0;

    loop {
      let sentinel = header.sentinel.as_inner_ref();
      let (sentinel_node_size, head_node_offset) = decode_segment_node(*sentinel);

      // free list is empty
      if sentinel_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && head_node_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return discarded;
      }

      let head = self.get_segment_node(head_node_offset);
      let head_node_size_and_next_node_offset = head.as_inner_ref();
      let (head_node_size, next_node_offset) =
        decode_segment_node(*head_node_size_and_next_node_offset);

      // Safety: the `next` and `node_size` are valid, because they just come from the sentinel.
      let segment_node = unsafe { Segment::from_offset(self, head_node_offset, head_node_size) };

      *header.sentinel.as_inner_mut() = encode_segment_node(sentinel_node_size, next_node_offset);

      // incresase the discarded memory.

      #[cfg(feature = "tracing")]
      tracing::debug!("discard {} bytes", segment_node.data_size);
      self.header_mut().discarded += segment_node.data_size;

      discarded += segment_node.data_size;
    }
  }

  /// Returns `true` if this offset and size is valid for a segment node.
  #[inline]
  fn validate_segment(&self, offset: u32, size: u32) -> bool {
    if offset == 0 || size == 0 {
      return false;
    }

    let aligned_offset = align_offset::<u64>(offset) as usize;
    let padding = aligned_offset - offset as usize;
    let segmented_node_size = padding + SEGMENT_NODE_SIZE;
    if segmented_node_size >= size as usize {
      return false;
    }

    let available_bytes = size - segmented_node_size as u32;
    if available_bytes < self.header().min_segment_size {
      return false;
    }

    true
  }

  #[inline]
  fn try_new_segment(&self, offset: u32, size: u32) -> Option<Segment> {
    if offset == 0 || size == 0 {
      return None;
    }

    let aligned_offset = align_offset::<u64>(offset) as usize;
    let padding = aligned_offset - offset as usize;
    let segmented_node_size = padding + SEGMENT_NODE_SIZE;
    if segmented_node_size >= size as usize {
      self.increase_discarded(size);
      return None;
    }

    let available_bytes = size - segmented_node_size as u32;
    if available_bytes < self.header().min_segment_size {
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
  fn get_segment_node(&self, offset: u32) -> &UnsafeCell<u64> {
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
    let mut current: &UnsafeCell<u64> = &header.sentinel;

    loop {
      let current_node = current.as_inner_ref();
      let (node_size, next_node_offset) = decode_segment_node(*current_node);

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
    use super::sealed::RefCounter;

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
