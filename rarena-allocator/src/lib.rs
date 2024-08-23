#![doc = include_str!("../README.md")]
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

#[cfg(not(any(feature = "std", feature = "alloc")))]
compile_error!("`rarena-allocator` requires either the 'std' or 'alloc' feature to be enabled");

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

mod error;
pub use error::*;

mod options;
pub use options::*;

use core::mem;

const FREELIST_OFFSET: usize = 1;
const FREELIST_SIZE: usize = mem::size_of::<Freelist>();
const MAGIC_TEXT: [u8; 2] = *b"al";
const MAGIC_TEXT_OFFSET: usize = FREELIST_OFFSET + FREELIST_SIZE;
const MAGIC_TEXT_SIZE: usize = MAGIC_TEXT.len();
const MAGIC_VERISON_OFFSET: usize = MAGIC_TEXT_OFFSET + MAGIC_TEXT_SIZE;
const MAGIC_VERISON_SIZE: usize = mem::size_of::<u16>();
const VERSION_OFFSET: usize = MAGIC_VERISON_OFFSET + MAGIC_VERISON_SIZE;
const VERSION_SIZE: usize = mem::size_of::<u16>();
const CURRENT_VERSION: u16 = 0;
const SENTINEL_SEGMENT_NODE_OFFSET: u32 = u32::MAX;
const SENTINEL_SEGMENT_NODE_SIZE: u32 = u32::MAX;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
static PAGE_SIZE: std::sync::LazyLock<u32> = std::sync::LazyLock::new(|| {
  #[cfg(not(windows))]
  {
    rustix::param::page_size() as u32
  }

  #[cfg(windows)]
  {
    use winapi::um::sysinfoapi::{GetSystemInfo, SYSTEM_INFO};

    unsafe {
      let mut system_info: SYSTEM_INFO = std::mem::zeroed();
      GetSystemInfo(&mut system_info);
      system_info.dwPageSize
    }
  }
});

/// Enumeration of possible methods to seek within an [`Arena`] allocator.
///
#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum ArenaPosition {
  /// Sets the offset to the provided number of bytes.
  Start(u32),

  /// Sets the offset to the capacity of the ARENA minus the provided number of bytes.
  End(u32),

  /// Sets the offset to the current position plus the specified number of
  /// bytes.
  ///
  /// It is possible to seek beyond the end of an object, but it's an error to
  /// seek before byte 0.
  Current(i64),
}

bitflags::bitflags! {
  #[derive(Clone, Copy)]
  struct MemoryFlags: u8 {
    const ON_DISK = 0b0000_0001;
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    const MMAP = 0b0000_0010;
  }
}

mod common {
  use core::{mem, ptr};

  #[cfg(not(feature = "loom"))]
  pub(crate) use core::cell::UnsafeCell;
  #[cfg(not(feature = "loom"))]
  pub(crate) use std::alloc::{alloc_zeroed, dealloc, Layout};

  #[cfg(feature = "loom")]
  pub(crate) use loom::{
    alloc::{alloc_zeroed, dealloc, Layout},
    cell::UnsafeCell,
  };

  #[cfg(not(feature = "loom"))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(feature = "loom")]
  pub(crate) use loom::sync::atomic::*;

  pub(crate) trait UnsafeCellExt<T> {
    fn as_inner_ptr(&self) -> *const T;
    fn as_inner_mut(&self) -> *mut T;
    #[inline]
    fn as_inner_ref(&self) -> &T {
      unsafe { &*self.as_inner_ptr() }
    }
    #[inline]
    #[allow(clippy::mut_from_ref)]
    fn as_inner_ref_mut(&self) -> &mut T {
      unsafe { &mut *self.as_inner_mut() }
    }
  }

  impl<T> UnsafeCellExt<T> for core::cell::UnsafeCell<T> {
    #[inline]
    fn as_inner_ptr(&self) -> *const T {
      self.get()
    }

    #[inline]
    fn as_inner_mut(&self) -> *mut T {
      self.get()
    }
  }

  #[cfg(feature = "loom")]
  impl<T> UnsafeCellExt<T> for loom::cell::UnsafeCell<T> {
    #[inline]
    fn as_inner_ptr(&self) -> *const T {
      unsafe { self.get().deref() }
    }

    #[inline]
    fn as_inner_mut(&self) -> *mut T {
      unsafe { self.get_mut().deref() }
    }
  }

  #[derive(Debug)]
  pub(super) struct AlignedVec {
    pub(super) ptr: ptr::NonNull<u8>,
    pub(super) cap: usize,
    pub(super) align: usize,
  }

  impl Drop for AlignedVec {
    #[inline]
    fn drop(&mut self) {
      if self.cap != 0 {
        unsafe {
          dealloc(self.ptr.as_ptr(), self.layout());
        }
      }
    }
  }

  impl AlignedVec {
    #[inline]
    pub(super) fn new<H>(capacity: usize, align: usize) -> Self {
      let align = align.max(mem::align_of::<H>());
      assert!(
        capacity <= Self::max_capacity(align),
        "`capacity` cannot exceed isize::MAX - {}",
        align - 1
      );

      let ptr = unsafe {
        let layout = Layout::from_size_align_unchecked(capacity, align);
        let ptr = alloc_zeroed(layout);
        if ptr.is_null() {
          std::alloc::handle_alloc_error(layout);
        }
        ptr::NonNull::new_unchecked(ptr)
      };

      Self {
        ptr,
        cap: capacity,
        align,
      }
    }

    #[inline]
    pub(super) const fn max_capacity(align: usize) -> usize {
      isize::MAX as usize - (align - 1)
    }

    #[inline]
    pub(super) const fn layout(&self) -> std::alloc::Layout {
      unsafe { std::alloc::Layout::from_size_align_unchecked(self.cap, self.align) }
    }

    #[inline]
    pub(super) fn as_mut_ptr(&mut self) -> *mut u8 {
      self.ptr.as_ptr()
    }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn invalid_data<E: std::error::Error + Send + Sync + 'static>(e: E) -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, e)
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn bad_magic() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "arena has bad magic")
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn bad_freelist() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "freelist mismatch")
}

#[inline]
const fn decode_segment_node(val: u64) -> (u32, u32) {
  ((val >> 32) as u32, val as u32)
}

#[inline]
const fn encode_segment_node(size: u32, next: u32) -> u64 {
  ((size as u64) << 32) | next as u64
}

/// Calculates the aligned offset for a given type `T` starting from `current_offset`.
///
/// This function aligns the given `current_offset` to the next boundary that satisfies the alignment requirements of type `T`.
///
/// # Parameters
///
/// - `current_offset`: The initial offset that needs to be aligned.
///
/// # Returns
///
/// The aligned offset that is the next multiple of the alignment requirement of type `T`.
///
/// # Examples
///
/// ```ignore
/// use std::mem;
///
/// #[repr(C, align(8))]
/// struct Meta {
///     a: u64,
///     b: u64,
/// }
///
/// let initial_offset: u32 = 1;
/// let aligned_offset = align_offset::<Meta>(initial_offset);
/// assert_eq!(aligned_offset, 8);
/// ```
///
/// # Explanation
///
/// - Given an `alignment` of type `T`, this function calculates the next aligned offset from `current_offset`.
/// - It ensures that the result is a multiple of `alignment` by adding `alignment - 1` to `current_offset` and then clearing the lower bits using bitwise AND with the negation of `alignment - 1`.
///
/// ```ignore
/// let alignment = mem::align_of::<T>() as u32;
/// (current_offset + alignment - 1) & !(alignment - 1)
/// ```
#[inline]
const fn align_offset<T>(current_offset: u32) -> u32 {
  let alignment = core::mem::align_of::<T>() as u32;
  (current_offset + alignment - 1) & !(alignment - 1)
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

#[cfg(feature = "std")]
macro_rules! write_byte_order {
  ($write_name:ident::$put_name:ident::$converter:ident($ty:ident, $endian:literal)) => {
    paste::paste! {
      #[doc = "Write a `" $ty "` value into the buffer in " $endian " byte order, return an error if the buffer does not have enough space."]
      #[inline]
      #[cfg(feature = "std")]
      pub fn $write_name(&mut self, value: $ty) -> std::io::Result<()> {
        self.$put_name(value).map_err(|e| std::io::Error::new(std::io::ErrorKind::WriteZero, e))
      }
    }
  }
}

macro_rules! put_byte_order {
  ($name:ident::$converter:ident($ty:ident, $endian:literal)) => {
    paste::paste! {
      #[doc = "Put a `" $ty "` value into the buffer in " $endian " byte order, return an error if the buffer does not have enough space."]
      #[inline]
      pub fn $name(&mut self, value: $ty) -> Result<(), BufferTooSmall> {
        const SIZE: usize = core::mem::size_of::<$ty>();

        if self.len + SIZE > self.capacity() {
          return Err(BufferTooSmall {
            remaining: self.capacity() - self.len,
            want: SIZE,
          });
        }

        // SAFETY: We have checked the buffer size.
        unsafe { self. [< $name _unchecked >](value); }
        Ok(())
      }

      #[doc = "Put a `" $ty "` value into the buffer in " $endian " byte order, without doing bounds checking."]
      ///
      #[doc = "For a safe alternative see [`" $name "`](Self::" $name ")."]
      ///
      /// # Safety
      ///
      /// Calling this method if the buffer does not have enough space to hold the value is *[undefined behavior]*.
      ///
      /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
      #[inline]
      pub unsafe fn [< $name _unchecked >] (&mut self, value: $ty) {
        const SIZE: usize = core::mem::size_of::<$ty>();

        let cur = self.len;
        let buf = self.buffer_mut();
        buf[cur..cur + SIZE].copy_from_slice(&value.$converter());
        self.len += SIZE;
      }
    }
  }
}

macro_rules! impl_bytes_mut_utils {
  (align) => {
    /// Add paddings to the buffer according to the alignment of `T`.
    ///
    /// Returns a well-aligned pointer for `T`
    #[inline]
    pub fn align_to<T>(&mut self) -> Result<NonNull<T>, BufferTooSmall> {
      if mem::size_of::<T>() == 0 {
        return Ok(NonNull::dangling());
      }

      let align_offset = crate::align_offset::<T>(self.allocated.memory_offset + self.len as u32);

      if align_offset > self.allocated.memory_offset + self.allocated.memory_size {
        return Err(BufferTooSmall {
          remaining: self.allocated.memory_size as usize - self.len,
          want: align_offset as usize - self.len - self.allocated.memory_offset as usize,
        });
      }

      self.len = (align_offset - self.allocated.memory_offset) as usize;
      // SAFETY: We have checked the buffer size, and apply the align
      Ok(unsafe {
        NonNull::new_unchecked(self.as_mut_ptr().add(self.len).cast::<T>())
      })
    }


    /// Put `T` into the buffer, return an error if the buffer does not have enough space.
    ///
    /// You may want to use [`put_aligned`] instead of this method.
    ///
    /// # Safety
    ///
    /// - Must invoke [`align_to`] before invoking this method, if `T` is not ZST.
    /// - If `T` needs to be dropped and callers invoke [`RefMut::detach`],
    ///   then the caller must ensure that the `T` is dropped before the ARENA is dropped.
    ///   Otherwise, it will lead to memory leaks.
    ///
    /// - If this is file backed ARENA, then `T` must be recoverable from bytes.
    ///   1. Types require allocation are not recoverable.
    ///   2. Pointers are not recoverable, like `*const T`, `*mut T`, `NonNull` and any structs contains pointers,
    ///      although those types are on stack, but they cannot be recovered, when reopens the file.
    pub unsafe fn put<T>(&mut self, val: T) -> Result<&mut T, BufferTooSmall> {
      let size = core::mem::size_of::<T>();

      if self.len + size > self.capacity() {
        return Err(BufferTooSmall {
          remaining: self.capacity() - self.len,
          want: size,
        });
      }

      // SAFETY: We have checked the buffer size.
      let ptr = self.as_mut_ptr().add(self.len).cast::<T>();
      ptr.write(val);
      self.len += size;
      Ok(&mut *ptr)
    }

    /// Put `T` into the buffer, return an error if the buffer does not have enough space.
    ///
    /// # Safety
    ///
    /// - If `T` needs to be dropped and callers invoke [`RefMut::detach`],
    ///   then the caller must ensure that the `T` is dropped before the ARENA is dropped.
    ///   Otherwise, it will lead to memory leaks.
    ///
    /// - If this is file backed ARENA, then `T` must be recoverable from bytes.
    ///   1. Types require allocation are not recoverable.
    ///   2. Pointers are not recoverable, like `*const T`, `*mut T`, `NonNull` and any structs contains pointers,
    ///      although those types are on stack, but they cannot be recovered, when reopens the file.
    pub unsafe fn put_aligned<T>(&mut self, val: T) -> Result<&mut T, BufferTooSmall> {
      let mut ptr = self.align_to::<T>()?;

      ptr.as_ptr().write(val);
      self.len += ::core::mem::size_of::<T>();
      Ok(ptr.as_mut())
    }
  };
  (slice) => {
    /// Put a bytes slice into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_slice(&mut self, slice: &[u8]) -> Result<(), BufferTooSmall> {
      let size = slice.len();

      if self.len + size > self.capacity() {
        return Err(BufferTooSmall {
          remaining: self.capacity() - self.len,
          want: size,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { self.put_slice_unchecked(slice); }
      Ok(())
    }

    /// Put a bytes slice into the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`put_slice`](Self::put_slice).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough space to hold the slice is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn put_slice_unchecked(&mut self, slice: &[u8]) {
      let size = slice.len();
      let cur = self.len;
      let buf = self.buffer_mut();
      buf[cur..cur + size].copy_from_slice(slice);
      self.len += size;
    }
  };
  ($($ty:ident), +$(,)?) => {
    $(
      paste::paste! {
        put_byte_order!([< put_ $ty _be>]::to_be_bytes($ty, "big-endian"));
        put_byte_order!([< put_ $ty _le >]::to_le_bytes($ty, "little-endian"));
        put_byte_order!([< put_ $ty _ne >]::to_ne_bytes($ty, "native-endian"));
        #[cfg(feature="std")]
        write_byte_order!([< write_ $ty _be>]::[< put_ $ty _be>]::to_be_bytes($ty, "big-endian"));
        #[cfg(feature="std")]
        write_byte_order!([< write_ $ty _le >]::[< put_ $ty _le >]::to_le_bytes($ty, "little-endian"));
        #[cfg(feature="std")]
        write_byte_order!([< write_ $ty _ne >]::[< put_ $ty _ne >]::to_ne_bytes($ty, "native-endian"));
      }
    )*
  };
  (8) => {
    /// Put a `u8` value into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_u8(&mut self, value: u8) -> Result<(), BufferTooSmall> {
      const SIZE: usize = core::mem::size_of::<u8>();

      if self.len + SIZE > self.capacity() {
        return Err(BufferTooSmall {
          remaining: self.capacity() - self.len,
          want: SIZE,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { self.put_u8_unchecked(value); }
      Ok(())
    }

    /// Put a `u8` value into the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`put_u8`](Self::put_u8).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough space to hold the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn put_u8_unchecked(&mut self, value: u8) {
      const SIZE: usize = core::mem::size_of::<u8>();

      let cur = self.len;
      let buf = self.buffer_mut();
      buf[cur..cur + SIZE].copy_from_slice(&[value]);
      self.len += SIZE;
    }

    /// Put a `i8` value into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_i8(&mut self, value: i8) -> Result<(), BufferTooSmall> {
      self.put_u8(value as u8)
    }

    /// Put a `i8` value into the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`put_i8`](Self::put_i8).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough space to hold the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn put_i8_unchecked(&mut self, value: i8) {
      self.put_u8_unchecked(value as u8)
    }
  };
}

macro_rules! get_byte_order {
  ($name:ident::$converter:ident($ty:ident, $endian:literal)) => {
    paste::paste! {
      #[doc = "Get a `" $ty "` value from the buffer in " $endian " byte order, return an error if the buffer does not have enough bytes."]
      #[inline]
      pub fn $name(&mut self) -> Result<$ty, NotEnoughBytes> {
        const SIZE: usize = core::mem::size_of::<$ty>();

        if self.len < SIZE {
          return Err(NotEnoughBytes {
            remaining: self.len,
            read: SIZE,
          });
        }

        // SAFETY: We have checked the buffer size.
        unsafe { Ok(self.[< $name _unchecked >]()) }
      }

      #[doc = "Get a `" $ty "` value from the buffer in " $endian " byte order, without doing bounds checking."]
      ///
      #[doc = "For a safe alternative see [`" $name "`](Self::" $name ")."]
      ///
      /// # Safety
      ///
      /// Calling this method if the buffer does not have enough bytes to read the value is *[undefined behavior]*.
      ///
      /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
      #[inline]
      pub unsafe fn [< $name _unchecked >](&mut self) -> $ty {
        const SIZE: usize = core::mem::size_of::<$ty>();

        let cur = self.len - SIZE;
        let buf = self.buffer();
        let value = <$ty>::from_be_bytes(buf[cur..cur + SIZE].try_into().unwrap());
        self.len -= SIZE;
        value
      }
    }
  }
}

macro_rules! impl_bytes_utils {
  (slice) => {
    /// Get a byte slice from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_slice(&self, size: usize) -> Result<&[u8], NotEnoughBytes> {
      if self.len < size {
        return Err(NotEnoughBytes {
          remaining: self.len,
          read: size,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { Ok(self.get_slice_unchecked(size)) }
    }

    /// Get a byte slice from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_slice`](Self::get_slice).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough bytes to read the slice is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_slice_unchecked(&self, size: usize) -> &[u8] {
      let buf = self.buffer();
      &buf[..size]
    }

    /// Get a mutable byte slice from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_slice_mut(&mut self, size: usize) -> Result<&mut [u8], NotEnoughBytes> {
      if self.len < size {
        return Err(NotEnoughBytes {
          remaining: self.len,
          read: size,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { Ok(self.get_slice_mut_unchecked(size)) }
    }

    /// Get a mutable byte slice from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_slice_mut`](Self::get_slice_mut).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough bytes to read the slice is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_slice_mut_unchecked(&mut self, size: usize) -> &mut [u8] {
      let buf = self.buffer_mut();
      &mut buf[..size]
    }
  };
  ($($ty:ident), +$(,)?) => {
    $(
      paste::paste! {
        get_byte_order!([< get_ $ty _be >]::from_be_bytes($ty, "big-endian"));
        get_byte_order!([< get_ $ty _le >]::from_le_bytes($ty, "little-endian"));
        get_byte_order!([< get_ $ty _ne >]::from_ne_bytes($ty, "native-endian"));
      }
    )*
  };
  (8) => {
    /// Get a `u8` value from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_u8(&mut self) -> Result<u8, NotEnoughBytes> {
      if self.len < 1 {
        return Err(NotEnoughBytes {
          remaining: self.len,
          read: 1,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { Ok(self.get_u8_unchecked()) }
    }

    /// Get a `u8` value from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_u8`](Self::get_u8).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough bytes to read the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_u8_unchecked(&mut self) -> u8 {
      let cur = self.len - 1;
      let buf = self.buffer();
      let value = buf[cur];
      self.len -= 1;
      value
    }

    /// Get a `i8` value from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_i8(&mut self) -> Result<i8, NotEnoughBytes> {
      self.get_u8().map(|v| v as i8)
    }

    /// Get a `i8` value from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_i8`](Self::get_i8).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough bytes to read the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_i8_unchecked(&mut self) -> i8 {
      self.get_u8_unchecked() as i8
    }
  };
}

#[cfg(feature = "std")]
macro_rules! impl_write_in {
  () => {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
      self
        .put_slice(buf)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::WriteZero, e))
        .map(|_| buf.len())
    }

    #[inline(always)]
    fn flush(&mut self) -> std::io::Result<()> {
      Ok(())
    }
  };
}

macro_rules! impl_write {
  ($ident: ident) => {
    #[cfg(feature = "std")]
    impl std::io::Write for $ident {
      impl_write_in!();
    }
  };
  ($ident: ident<'a>) => {
    #[cfg(feature = "std")]
    impl<'a> std::io::Write for $ident<'a> {
      impl_write_in!();
    }
  };
  ($ident: ident<T>) => {
    #[cfg(feature = "std")]
    impl<T> std::io::Write for $ident<T> {
      impl_write_in!();
    }
  };
}

/// Lock-free ARENA allocator can be used in concurrent environments.
pub mod sync;

/// ARENA allocator for single-threaded environments.
pub mod unsync;
