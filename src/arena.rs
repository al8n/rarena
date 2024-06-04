use core::{
  fmt,
  mem::{self, MaybeUninit},
  ops,
  ptr::{self, NonNull},
  slice,
};

use crossbeam_utils::Backoff;

use crate::{common::*, ArenaOptions};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use crate::{MmapOptions, OpenOptions};

#[allow(unused_imports)]
use std::boxed::Box;

mod backed;
use backed::*;

mod bytes;
pub use bytes::*;

mod object;
pub use object::*;

#[cfg(test)]
mod tests;

const OVERHEAD: usize = mem::size_of::<Header>();
const SLOW_RETRIES: usize = 5;

#[derive(Debug)]
#[repr(C)]
pub(super) struct Header {
  /// The sentinel node for the ordered free list.
  sentinel: AtomicU64,
  allocated: AtomicU32,
  min_segment_size: AtomicU32,
}

impl Header {
  #[inline]
  fn new(size: u32, min_segment_size: u32) -> Self {
    Self {
      allocated: AtomicU32::new(size),
      sentinel: AtomicU64::new(encode_segment_node(u32::MAX, u32::MAX)),
      min_segment_size: AtomicU32::new(min_segment_size),
    }
  }
}

/// An error indicating that the arena is full
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct ArenaError;

impl core::fmt::Display for ArenaError {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "allocation failed because arena is full")
  }
}

#[cfg(feature = "std")]
impl std::error::Error for ArenaError {}

/// Arena should be lock-free
pub struct Arena {
  write_data_ptr: NonNull<u8>,
  read_data_ptr: *const u8,
  header_ptr: *const u8,
  ptr: *mut u8,
  data_offset: u32,
  inner: AtomicPtr<()>,
  cap: u32,
}

impl fmt::Debug for Arena {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let header = self.header();
    let allocated = header.allocated.load(Ordering::Acquire);

    // Safety:
    // The ptr is always non-null, we only deallocate it when the arena is dropped.
    let data =
      unsafe { slice::from_raw_parts(self.read_data_ptr, (allocated - self.data_offset) as usize) };

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
      let shared: *mut Shared = self.inner.load(Ordering::Relaxed).cast();

      let old_size = (*shared).refs.fetch_add(1, Ordering::Release);
      if old_size > usize::MAX >> 1 {
        abort();
      }

      // Safety:
      // The ptr is always non-null, and the data is only deallocated when the
      // last Arena is dropped.
      Self {
        write_data_ptr: self.write_data_ptr,
        read_data_ptr: self.read_data_ptr,
        header_ptr: self.header_ptr,
        ptr: self.ptr,
        data_offset: self.data_offset,
        inner: AtomicPtr::new(shared as _),
        cap: self.cap,
      }
    }
  }
}

impl Arena {
  /// Returns the number of bytes allocated by the arena.
  #[inline]
  pub fn size(&self) -> usize {
    self.header().allocated.load(Ordering::Acquire) as usize
  }

  /// Returns the capacity of the arena.
  #[inline]
  pub fn capacity(&self) -> usize {
    self.cap as usize
  }

  /// Returns the number of bytes remaining bytes can be allocated by the arena.
  #[inline]
  pub fn remaining(&self) -> usize {
    (self.cap as usize).saturating_sub(self.size())
  }

  /// Returns the number of references to the arena.
  #[inline]
  pub fn refs(&self) -> usize {
    unsafe {
      let shared: *mut Shared = self.inner.load(Ordering::Relaxed).cast();

      (*shared).refs.load(Ordering::Acquire)
    }
  }

  #[inline]
  pub(super) fn header(&self) -> &Header {
    // Safety:
    // The header is always non-null, we only deallocate it when the arena is dropped.
    unsafe { &*(self.header_ptr as *const _) }
  }
}

unsafe impl Send for Arena {}
unsafe impl Sync for Arena {}

impl Arena {
  /// Creates a new ARENA with the given capacity,
  #[inline]
  pub fn new(opts: ArenaOptions) -> Self {
    Self::new_in(Shared::new_vec(
      opts.capacity(),
      opts.maximum_alignment(),
      opts.minimum_segment_size(),
    ))
  }

  /// Creates a new ARENA backed by a mmap with the given capacity.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Shared::map_mut(
      path,
      open_options,
      mmap_options,
      opts.maximum_alignment(),
      opts.minimum_segment_size(),
    )
    .map(Self::new_in)
  }

  /// Creates a new read only ARENA backed by a mmap with the given capacity.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Shared::map(path, open_options, mmap_options).map(Self::new_in)
  }

  /// Creates a new ARENA backed by an anonymous mmap with the given capacity.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub fn map_anon(opts: ArenaOptions, mmap_options: MmapOptions) -> std::io::Result<Self> {
    Shared::map_anon(
      mmap_options,
      opts.maximum_alignment(),
      opts.minimum_segment_size(),
    )
    .map(Self::new_in)
  }

  /// Allocates a `T` in the ARENA.
  #[inline]
  pub fn alloc<T>(&self) -> Result<RefMut<'_, T>, ArenaError> {
    if mem::size_of::<T>() == 0 {
      return Ok(RefMut::new_zst(self));
    }

    let size_with_padding = Self::pad::<T>();
    let mut bytes = self.alloc_bytes(size_with_padding as u32)?;
    let ptr = bytes.as_mut_ptr();
    bytes.detach();

    if mem::needs_drop::<T>() {
      unsafe {
        let object_ptr: *mut MaybeUninit<T> =
          ptr.add(size_with_padding - mem::size_of::<T>()).cast();
        ptr::write(object_ptr, MaybeUninit::uninit());

        Ok(RefMut::new(
          ptr::read(object_ptr),
          bytes.offset as u32,
          bytes.cap,
          self,
        ))
      }
    } else {
      // SAFETY: The ptr is valid and well aligned.
      unsafe {
        let object_ptr = ptr.add(size_with_padding - mem::size_of::<T>());
        Ok(RefMut::new_inline(
          NonNull::new_unchecked(object_ptr.cast()),
          bytes.offset as u32,
          bytes.cap,
          self,
        ))
      }
    }
  }

  /// Allocates an owned slice of memory in the ARENA.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc_bytes`](Self::alloc_bytes).
  #[inline]
  pub fn alloc_bytes_owned(&self, size: u32) -> Result<BytesMut, ArenaError> {
    self.alloc_bytes(size).map(|mut b| b.to_owned())
  }

  /// Allocates a slice of memory in the ARENA.
  ///
  /// The [`BytesRefMut`] is zeroed out.
  ///
  /// If you want a [`BytesMut`], see [`alloc_bytes_owned`](Self::alloc_bytes_owned).
  pub fn alloc_bytes(&self, size: u32) -> Result<BytesRefMut, ArenaError> {
    if size == 0 {
      return Ok(BytesRefMut::null(self));
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
          unsafe {
            // SAFETY: The len and offset is valid.
            let mut bytes = BytesRefMut::new(self, size, offset);
            bytes.fill(0);
            return Ok(bytes);
          }
        }
        Err(x) => allocated = x,
      }
    }

    // allocate through slow path
    for _ in 0..SLOW_RETRIES {
      match self.alloc_slow_path(size) {
        Ok(bytes) => return Ok(bytes),
        Err(_) => continue,
      }
    }

    Err(ArenaError)
  }

  /// It is like a pop operation, we will always allocate from the largest segment.
  fn alloc_slow_path(&self, size: u32) -> Result<BytesRefMut, ArenaError> {
    let backoff = Backoff::new();
    let header = self.header();

    loop {
      let head = header.sentinel.load(Ordering::Acquire);
      let (next, node_size) = decode_segment_node(head);
      // free list is empty
      if next == u32::MAX && node_size == u32::MAX {
        return Err(ArenaError);
      }

      if node_size == 0 {
        // The current head is removed from the list, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // The larget segment does not have enough space to allocate, so just return err.
      if size > node_size {
        return Err(ArenaError);
      }

      // CAS to remove the current
      let removed_head = encode_segment_node(next, 0);
      if header
        .sentinel
        .compare_exchange_weak(head, removed_head, Ordering::AcqRel, Ordering::Relaxed)
        .is_err()
      {
        // wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // We have successfully mark the head is removed, then we need to let head node's next point to the next node.
      let next_node = unsafe { self.get_segment_node(next) };
      let next_node_val = next_node.load(Ordering::Acquire);

      match header.sentinel.compare_exchange(
        removed_head,
        next_node_val,
        Ordering::AcqRel,
        Ordering::Relaxed,
      ) {
        Ok(_) => {
          // We have successfully remove the head node from the list.
          // Then we can allocate the memory.
          unsafe {
            // SAFETY: The len and offset is valid.
            let mut bytes = BytesRefMut::new(self, size, next);
            bytes.fill(0);

            // give back the remaining memory to the free list.
            self.dealloc(next + size, node_size - size);
            return Ok(bytes);
          }
        }
        Err(current_sentinel) => {
          let (_, size) = decode_segment_node(current_sentinel);
          if size == 0 {
            // The current head is removed from the list, wait other thread to make progress.
            backoff.snooze();
            continue;
          }

          backoff.spin();
        }
      }
    }
  }

  fn dealloc(&self, offset: u32, size: u32) {
    // check if we have enough space to allocate a new segment in this segment.
    if !self.validate_segment(offset, size) {
      return;
    }

    let backoff = Backoff::new();

    unsafe {
      let ptr = self.write_data_ptr.as_ptr().add(offset as usize);

      // clear the memory
      ptr::write_bytes(ptr, 0, size as usize);
      let header = self.header();

      loop {
        let (prev, next) = self.find_free_list_position(size);

        let prev_node = prev
          .map(|p| self.get_segment_node(p))
          .unwrap_or(&header.sentinel);
        let next_node_offset = next.unwrap_or(u32::MAX);

        self.write_segment_node(next_node_offset, offset, size);

        // CAS prev_node's next points to the new_node
        let prev_node_val = prev_node.load(Ordering::Acquire);
        let (_, prev_node_size) = decode_segment_node(prev_node_val);

        // the prev is removed from the list, then we need to refind the position.
        if prev_node_size == 0 {
          // wait other thread to make progress.
          backoff.snooze();
          continue;
        }

        match prev_node.compare_exchange(
          prev_node_val,
          encode_segment_node(offset, size),
          Ordering::AcqRel,
          Ordering::Relaxed,
        ) {
          Ok(_) => break,
          Err(current_prev) => {
            let (_, size) = decode_segment_node(current_prev);
            // the prev is removed from the list, then we need to refind the position.
            if size == 0 {
              // wait other thread to make progress.
              backoff.snooze();
              continue;
            }

            backoff.spin();
          }
        }
      }
    }
  }

  /// Returns `true` if this offset and size is valid for a segment node.
  #[inline]
  fn validate_segment(&self, offset: u32, size: u32) -> bool {
    unsafe {
      let ptr = self.write_data_ptr.as_ptr().add(offset as usize);
      let aligned_offset = ptr.align_offset(mem::align_of::<AtomicU64>());
      let want = aligned_offset + mem::size_of::<AtomicU64>() + mem::size_of::<u32>();
      if want >= size as usize {
        return false;
      }

      if size < self.header().min_segment_size.load(Ordering::Acquire) {
        return false;
      }

      true
    }
  }

  fn find_free_list_position(&self, val: u32) -> (Option<u32>, Option<u32>) {
    let header = self.header();
    let mut current = &header.sentinel;

    let mut prev = 0;
    let backoff = Backoff::new();
    loop {
      let current_node = current.load(Ordering::Acquire);
      let (current_next, current_node_size) = decode_segment_node(current_node);

      // we reach the tail of the list
      if current_next == u32::MAX {
        // the list is empty
        if prev == 0 {
          return (None, None);
        }

        return (Some(prev), None);
      }

      // the current is marked as removed
      if current_node_size == 0 {
        // wait other thread to remove the node.
        backoff.snooze();
        continue;
      }

      // the size is smaller than or equal to the val
      // then the value should be inserted before the current node
      if val >= current_node_size {
        if prev == 0 {
          return (None, Some(current_next));
        }

        return (Some(prev), Some(current_next));
      }

      let next = unsafe { self.get_segment_node(current_next) };

      prev = current_next;
      current = next;
      backoff.spin();
    }
  }

  unsafe fn get_segment_node(&self, offset: u32) -> &AtomicU64 {
    let ptr = self.read_data_ptr.add(offset as usize);
    let aligned_offset = ptr.align_offset(mem::align_of::<AtomicU64>());
    let ptr = ptr.add(aligned_offset);
    &*(ptr as *const _)
  }

  unsafe fn write_segment_node(&self, next: u32, offset: u32, size: u32) -> u32 {
    let ptr = self.write_data_ptr.as_ptr().add(offset as usize);
    let aligned_offset = ptr.align_offset(mem::align_of::<AtomicU64>());
    let ptr = ptr.add(aligned_offset);
    let node = ptr as *mut AtomicU64;
    let node = &mut *node;
    node.store(encode_segment_node(next, size), Ordering::Release);
    offset
  }

  #[inline]
  fn new_in(mut shared: Shared) -> Self {
    // Safety:
    // The ptr is always non-null, we just initialized it.
    // And this ptr is only deallocated when the arena is dropped.
    let read_data_ptr = shared.as_ptr();
    let header_ptr = shared.header_ptr();
    let ptr = shared.null_mut();
    let write_data_ptr = shared
      .as_mut_ptr()
      .map(|p| unsafe { NonNull::new_unchecked(p) })
      .unwrap_or_else(NonNull::dangling);

    Self {
      cap: shared.cap(),
      write_data_ptr,
      read_data_ptr,
      header_ptr,
      ptr,
      data_offset: shared.data_offset as u32,
      inner: AtomicPtr::new(Box::into_raw(Box::new(shared)) as _),
    }
  }

  /// Flushes the memory-mapped file to disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub fn flush(&self) -> std::io::Result<()> {
    let shared = self.inner.load(Ordering::Acquire);
    {
      let shared: *mut Shared = shared.cast();
      unsafe { (*shared).flush() }
    }
  }

  /// Flushes the memory-mapped file to disk asynchronously.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub fn flush_async(&self) -> std::io::Result<()> {
    let shared = self.inner.load(Ordering::Acquire);
    {
      let shared: *mut Shared = shared.cast();
      unsafe { (*shared).flush_async() }
    }
  }

  #[inline]
  fn pad<T>() -> usize {
    let size = mem::size_of::<T>();
    let align = mem::align_of::<T>();
    size + align - 1
  }

  /// ## Safety:
  /// - The caller must make sure that `offset` must be less than the capacity of the arena.
  /// - The caller must make sure that `size` must be less than the capacity of the arena.
  /// - The caller must make sure that `offset + size` must be less than the capacity of the arena.
  #[inline]
  pub(super) const unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8] {
    if offset == 0 {
      return &[];
    }

    let ptr = self.get_pointer(offset);
    slice::from_raw_parts(ptr, size)
  }

  /// ## Safety:
  /// - The caller must make sure that `offset` must be less than the capacity of the arena.
  /// - The caller must make sure that `size` must be less than the capacity of the arena.
  /// - The caller must make sure that `offset + size` must be less than the capacity of the arena.
  #[allow(clippy::mut_from_ref)]
  #[inline]
  pub(super) unsafe fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8] {
    if offset == 0 {
      return &mut [];
    }

    let ptr = self.get_pointer_mut(offset);
    slice::from_raw_parts_mut(ptr, size)
  }

  /// ## Safety:
  /// - The caller must make sure that `offset` must be less than the capacity of the arena.
  #[inline]
  pub(super) const unsafe fn get_pointer<T>(&self, offset: usize) -> *const T {
    if offset == 0 {
      return self.ptr.cast();
    }
    self.read_data_ptr.add(offset).cast()
  }

  /// ## Safety:
  /// - The caller must make sure that `offset` must be less than the capacity of the arena.
  #[inline]
  pub(super) unsafe fn get_pointer_mut<T>(&self, offset: usize) -> *mut T {
    if offset == 0 {
      return self.ptr.cast();
    }
    self.write_data_ptr.as_ptr().add(offset).cast()
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    unsafe {
      self.inner.with_mut(|shared| {
        let shared: *mut Shared = shared.cast();
        // `Shared` storage... follow the drop steps from Arc.
        if (*shared).refs.fetch_sub(1, Ordering::Release) != 1 {
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
        (*shared).refs.load(Ordering::Acquire);
        // Drop the data
        let mut shared = Box::from_raw(shared);

        // Relaxed is enough here as we're in a drop, no one else can
        // access this memory anymore.
        shared.unmount();
      });
    }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn invalid_data<E: std::error::Error + Send + Sync + 'static>(e: E) -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, e)
}

#[inline]
const fn decode_segment_node(val: u64) -> (u32, u32) {
  ((val >> 32) as u32, val as u32)
}

#[inline]
const fn encode_segment_node(next: u32, size: u32) -> u64 {
  ((next as u64) << 32) | size as u64
}

#[inline(never)]
#[cold]
fn abort() -> ! {
  #[cfg(feature = "std")]
  {
    std::process::abort()
  }

  #[cfg(not(feature = "std"))]
  {
    struct Abort;
    impl Drop for Abort {
      fn drop(&mut self) {
        panic!();
      }
    }
    let _a = Abort;
    panic!("abort");
  }
}
