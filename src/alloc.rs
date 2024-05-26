use core::{
  fmt, mem, ops,
  ptr::{self, NonNull},
  slice,
};

use crate::common::*;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use crate::{MmapOptions, OpenOptions};

#[cfg(not(feature = "loom"))]
use crate::common::AtomicMut;

#[allow(unused_imports)]
use std::boxed::Box;

mod backed;
use backed::*;

mod sealed;
use sealed::Atomic;

mod bytes;
pub use bytes::*;

mod object;
pub use object::*;

// mod segment;
// use segment::*;

#[cfg(test)]
mod tests;

#[doc(hidden)]
pub trait Size:
  sealed::Sealed
  + ops::Add<Output = Self>
  + ops::Sub<Output = Self>
  + ops::Rem<Output = Self>
  + ops::Not<Output = Self>
  + ops::BitAnd<Output = Self>
  + fmt::Debug
  + Sized
  + Send
  + Sync
  + Copy
  + Eq
  + Ord
  + 'static
{
  const ZERO: Self;
  const ONE: Self;

  type Atomic: sealed::Atomic<Self>;

  fn to_usize(self) -> usize;

  fn to_u64(self) -> u64;

  fn from_usize(s: usize) -> Self;
}

impl Size for u32 {
  const ONE: Self = 1;
  const ZERO: Self = 0;

  type Atomic = AtomicU32;

  #[inline(always)]
  fn to_usize(self) -> usize {
    self as usize
  }

  #[inline(always)]
  fn to_u64(self) -> u64 {
    self as u64
  }

  #[inline(always)]
  fn from_usize(s: usize) -> Self {
    s as Self
  }
}

impl Size for u64 {
  const ONE: Self = 1;
  const ZERO: Self = 0;

  type Atomic = AtomicU64;

  #[inline(always)]
  fn to_usize(self) -> usize {
    self as usize
  }

  #[inline(always)]
  fn to_u64(self) -> u64 {
    self
  }

  #[inline(always)]
  fn from_usize(s: usize) -> Self {
    s as Self
  }
}

#[derive(Debug)]
#[repr(C)]
pub(super) struct Header<S: Size = u32> {
  allocated: S::Atomic,
}

impl<S: Size> Header<S> {
  #[inline]
  fn new(size: S) -> Self {
    Self {
      allocated: <S::Atomic as Atomic<S>>::new(size),
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
pub struct Arena<S: Size = u32> {
  write_data_ptr: NonNull<u8>,
  read_data_ptr: *const u8,
  header_ptr: *const Header<S>,
  ptr: *mut u8,
  data_offset: usize,
  inner: AtomicPtr<()>,
  cap: S,
}

impl<S: Size> core::fmt::Debug for Arena<S> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let header = self.header();
    let allocated = header.allocated.load(Ordering::Acquire).to_usize();

    // Safety:
    // The ptr is always non-null, we only deallocate it when the arena is dropped.
    let data = unsafe { slice::from_raw_parts(self.read_data_ptr, allocated - self.data_offset) };

    f.debug_struct("Arena")
      .field("cap", &self.cap)
      .field("header", header)
      .field("data", &data)
      .finish()
  }
}

impl<S: Size> Clone for Arena<S> {
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

impl<S: Size> Arena<S> {
  /// Returns the number of bytes allocated by the arena.
  #[inline]
  pub fn size(&self) -> usize {
    self.header().allocated.load(Ordering::Acquire).to_usize()
  }

  /// Returns the capacity of the arena.
  #[inline]
  pub fn capacity(&self) -> usize {
    self.cap.to_usize()
  }

  /// Returns the number of bytes remaining bytes can be allocated by the arena.
  #[inline]
  pub fn remaining(&self) -> usize {
    self.cap.to_usize().saturating_sub(self.size())
  }

  /// Returns the number of references to the arena.
  #[inline]
  pub fn refs(&self) -> usize {
    unsafe {
      let shared: *mut Shared = self.inner.load(Ordering::Relaxed).cast();

      (*shared).refs.load(Ordering::Acquire)
    }
  }

  /// Clears the ARENA.
  #[inline]
  pub fn clear(&self) {
    let header = self.header();
    header
      .allocated
      .store(S::from_usize(self.data_offset), Ordering::Release);
  }

  #[inline]
  pub(super) const fn header(&self) -> &Header<S> {
    // Safety:
    // The header is always non-null, we only deallocate it when the arena is dropped.
    unsafe { &*self.header_ptr }
  }
}

unsafe impl<S: Size> Send for Arena<S> {}
unsafe impl<S: Size> Sync for Arena<S> {}

impl<S: Size> Arena<S> {
  /// Creates a new ARENA with the given capacity,
  #[inline]
  pub fn new(cap: S) -> Self {
    Self::new_in(Shared::new_vec(cap))
  }

  /// Allocates an owned slice of memory in the ARENA.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc_bytes`](Self::alloc_bytes).
  #[inline]
  pub fn alloc_bytes_owned(&self, size: S) -> Result<BytesMut<S>, ArenaError> {
    self.alloc_bytes(size).map(|mut b| b.to_owned())
  }

  /// Allocates a slice of memory in the ARENA.
  ///
  /// The [`BytesRefMut`] is zeroed out.
  ///
  /// If you want a [`BytesMut`], see [`alloc_bytes_owned`](Self::alloc_bytes_owned).
  pub fn alloc_bytes(&self, size: S) -> Result<BytesRefMut<S>, ArenaError> {
    if size == S::ZERO {
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

    // TODO: check if the segmented list has enough space to allocate.

    Err(ArenaError)
  }

  /// Allocates an owned `T` in the ARENA.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc`](Self::alloc).
  #[inline]
  pub fn alloc_owned<T>(&self) -> Result<Owned<T, S>, ArenaError> {
    self.alloc::<T>().map(|mut r| r.to_owned())
  }

  /// Allocates `T` in the ARENA.
  pub fn alloc<T>(&self) -> Result<RefMut<T, S>, ArenaError> {
    let mem_t = mem::size_of::<T>();

    if mem_t == 0 {
      // SAFETY: T is zero-sized and zero-aligned.
      return Ok(unsafe { RefMut::null(self) });
    }

    let padded = Self::pad::<T>();
    let header = self.header();
    let mut current_allocated = header.allocated.load(Ordering::Acquire);

    loop {
      let want = current_allocated + padded;

      if want > self.cap {
        break;
      }

      match header.allocated.compare_exchange_weak(
        current_allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(current) => {
          // Return the aligned offset.
          let current = current.to_usize();
          let padded = padded.to_usize();
          let allocated = current + padded;
          let ptr_offset = allocated & !(mem::align_of::<T>() - 1);
          return Ok(RefMut::new(
            self,
            unsafe { NonNull::new_unchecked(self.ptr.add(ptr_offset).cast()) },
            current,
            padded,
          ));
        }
        Err(x) => {
          current_allocated = x;
        }
      }
    }

    Err(ArenaError)
  }

  /// Allocates an owned `T` in the ARENA.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc_unaligned`](Self::alloc_unaligned).
  #[inline]
  pub fn alloc_owned_unaligned<T>(&self) -> Result<Owned<T, S>, ArenaError> {
    self.alloc_unaligned::<T>().map(|mut r| r.to_owned())
  }

  /// Allocates `T` in the ARENA, without padding.
  pub fn alloc_unaligned<T>(&self) -> Result<RefMut<T, S>, ArenaError> {
    let mem_t = mem::size_of::<T>();
    // If size of T is zero, return early with a null reference.
    if mem_t == 0 {
      // SAFETY: T is zero-sized and zero-aligned.
      return Ok(unsafe { RefMut::null(self) });
    }

    // Delegate to alloc_bytes with the aligned size.
    let mut bytes_ref = self.alloc_bytes(S::from_usize(mem_t))?;
    // Detach it, so the bytes_ref will not be collected by ARENA when dropped.
    bytes_ref.detach = true;

    // Calculate the aligned pointer within the allocated bytes.
    let ptr = bytes_ref.as_mut_ptr();
    let ptr_offset = ptr as usize - self.write_data_ptr.as_ptr() as usize;

    Ok(RefMut::new(
      self,
      unsafe { NonNull::new_unchecked(ptr.cast()) },
      bytes_ref.offset,
      bytes_ref.cap,
    ))
  }

  fn dealloc(&self, _offset: usize, _size: usize, _used: usize) {
    // TODO: Implement deallocation logic
  }
}

impl<S: Size> Arena<S> {
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[inline]
  // pub(super) fn mmap_mut<P: AsRef<std::path::Path>>(
  //   path: P,
  //   open_options: OpenOptions,
  //   mmap_options: MmapOptions,
  //   min_cap: usize,
  //   alignment: usize,
  // ) -> std::io::Result<Self> {
  //   let min_cap = min_cap.saturating_add(OVERHEAD);
  //   Shared::mmap_mut(path, open_options, mmap_options, min_cap, alignment).map(Self::new_in)
  // }

  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[inline]
  // pub(super) fn mmap<P: AsRef<std::path::Path>>(
  //   path: P,
  //   open_options: OpenOptions,
  //   mmap_options: MmapOptions,
  //   min_cap: usize,
  //   alignment: usize,
  // ) -> std::io::Result<Self> {
  //   let min_cap = min_cap.saturating_add(OVERHEAD);
  //   Shared::mmap(path, open_options, mmap_options, min_cap, alignment).map(Self::new_in)
  // }

  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[inline]
  // pub(super) fn new_anonymous_mmap(
  //   mmap_options: MmapOptions,
  //   min_cap: usize,
  //   alignment: usize,
  // ) -> std::io::Result<Self> {
  //   let min_cap = min_cap.saturating_add(OVERHEAD);
  //   Shared::new_mmaped_anon(mmap_options, min_cap, alignment).map(Self::new_in)
  // }

  #[inline]
  fn new_in(mut shared: Shared<S>) -> Self {
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
      data_offset: shared.data_offset,
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

  // #[cfg(not(feature = "unaligned"))]
  // pub(super) fn alloc<T>(
  //   &self,
  //   size: u32,
  //   value_size: u32,
  //   align: u32,
  //   overflow: u32,
  // ) -> Result<AllocMeta, ArenaError> {
  //   let trailer_size = mem::size_of::<T>();
  //   let trailer_align = mem::align_of::<T>();

  //   // Pad the allocation with enough bytes to ensure the requested alignment.
  //   let padded = size as u64 + align as u64 - 1;
  //   let trailer_padded = trailer_size as u64 + trailer_align as u64 - 1;
  //   let header = self.header();
  //   let mut current_allocated = header.allocated.load(Ordering::Acquire);
  //   if current_allocated + padded + overflow as u64 + trailer_padded + value_size as u64
  //     > self.cap as u64
  //   {
  //     return Err(ArenaError);
  //   }

  //   loop {
  //     let want = current_allocated + padded + trailer_padded + value_size as u64;
  //     match header.allocated.compare_exchange_weak(
  //       current_allocated,
  //       want,
  //       Ordering::SeqCst,
  //       Ordering::Acquire,
  //     ) {
  //       Ok(current) => {
  //         // Return the aligned offset.
  //         let allocated = current + padded;
  //         let node_offset = (allocated as u32 - size) & !(align - 1);

  //         let allocated_for_trailer = allocated + trailer_padded;
  //         let value_offset =
  //           (allocated_for_trailer as u32 - trailer_size as u32) & !(trailer_align as u32 - 1);

  //         #[cfg(feature = "tracing")]
  //         tracing::trace!(
  //           "ARENA allocates {} bytes for a node",
  //           want - current_allocated
  //         );

  //         return Ok(AllocMeta {
  //           node_offset,
  //           value_offset,
  //           allocated: (want - current_allocated) as u32,
  //         });
  //       }
  //       Err(x) => {
  //         if x + padded + overflow as u64 + trailer_padded + value_size as u64 > self.cap as u64 {
  //           return Err(ArenaError);
  //         }

  //         current_allocated = x;
  //       }
  //     }
  //   }
  // }

  // #[cfg(not(feature = "unaligned"))]
  // pub(super) fn alloc_key(&self, size: u16) -> Result<(u32, u16), ArenaError> {
  //   let size = size as u64;
  //   let header = self.header();
  //   let mut current_allocated = header.allocated.load(Ordering::Acquire);
  //   if current_allocated + size > self.cap as u64 {
  //     return Err(ArenaError);
  //   }

  //   loop {
  //     let want = current_allocated + size;
  //     match header.allocated.compare_exchange_weak(
  //       current_allocated,
  //       want,
  //       Ordering::SeqCst,
  //       Ordering::Acquire,
  //     ) {
  //       Ok(current) => {
  //         // Return the aligned offset.
  //         #[cfg(feature = "tracing")]
  //         tracing::trace!("ARENA allocates {} bytes for a key", size);
  //         return Ok((current as u32, size as u16));
  //       }
  //       Err(x) => {
  //         if x + size > self.cap as u64 {
  //           return Err(ArenaError);
  //         }

  //         current_allocated = x;
  //       }
  //     }
  //   }
  // }

  // #[cfg(not(feature = "unaligned"))]
  // pub(super) fn alloc_value<T>(&self, size: u32) -> Result<(u32, u32), ArenaError> {
  //   let padded = Self::pad_value_and_trailer::<T>(size);
  //   let header = self.header();
  //   let mut current_allocated = header.allocated.load(Ordering::Acquire);
  //   if current_allocated + padded > self.cap as u64 {
  //     return Err(ArenaError);
  //   }

  //   loop {
  //     let want = current_allocated + padded;
  //     match header.allocated.compare_exchange_weak(
  //       current_allocated,
  //       want,
  //       Ordering::SeqCst,
  //       Ordering::Acquire,
  //     ) {
  //       Ok(current) => {
  //         // Return the aligned offset.
  //         let allocated = current + padded;
  //         let value_offset = (allocated as u32 - size) & !(mem::align_of::<T>() as u32 - 1);
  //         #[cfg(feature = "tracing")]
  //         tracing::trace!("ARENA allocates {} bytes for a value", padded);
  //         return Ok((value_offset, padded as u32));
  //       }
  //       Err(x) => {
  //         if x + padded > self.cap as u64 {
  //           return Err(ArenaError);
  //         }

  //         current_allocated = x;
  //       }
  //     }
  //   }
  // }

  #[inline]
  fn pad<T>() -> S {
    let size = mem::size_of::<T>();
    let align = mem::align_of::<T>();
    S::from_usize(size + align - 1)
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

impl<S: Size> Drop for Arena<S> {
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
