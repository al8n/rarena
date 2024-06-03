use core::{
  fmt, mem, ops,
  ptr::{self, NonNull},
  slice,
};

use crate::common::*;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use crate::{MmapOptions, OpenOptions};

#[allow(unused_imports)]
use std::boxed::Box;

mod backed;
use backed::*;

mod bytes;
pub use bytes::*;

#[cfg(test)]
mod tests;

const OVERHEAD: usize = mem::size_of::<Header>();

#[derive(Debug)]
#[repr(C)]
pub(super) struct Header {
  sentinel: AtomicU64,
  allocated: AtomicU32,
}

impl Header {
  #[inline]
  fn new(size: u32) -> Self {
    Self {
      allocated: AtomicU32::new(size),
      sentinel: AtomicU64::new(0),
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
  pub fn new(cap: u32, alignment: usize) -> Self {
    Self::new_in(Shared::new_vec(cap, alignment))
  }

  /// Creates a new ARENA backed by a mmap with the given capacity.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    alignment: usize,
  ) -> std::io::Result<Self> {
    Shared::map_mut(path, open_options, mmap_options, alignment).map(Self::new_in)
  }

  /// Creates a new read only ARENA backed by a mmap with the given capacity.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    alignment: usize,
  ) -> std::io::Result<Self> {
    Shared::map(path, open_options, mmap_options, alignment).map(Self::new_in)
  }

  /// Creates a new ARENA backed by an anonymous mmap with the given capacity.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub fn map_anon(mmap_options: MmapOptions, alignment: usize) -> std::io::Result<Self> {
    Shared::map_anon(mmap_options, alignment).map(Self::new_in)
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

    // TODO: check if the segmented list has enough space to allocate.

    Err(ArenaError)
  }

  fn dealloc(&self, _offset: usize, _size: usize, _used: usize) {
    // TODO: Implement deallocation logic
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
  fn _pad<T>() -> usize {
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
