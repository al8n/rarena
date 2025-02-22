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

mod allocator;
mod common;
mod error;
mod memory;
mod options;
mod sealed;

#[cfg(test)]
#[macro_use]
mod tests;

use core::mem;
use dbutils::checksum::{BuildChecksumer, Checksumer};

pub use allocator::Allocator;
pub use dbutils::checksum;
pub use either;
pub use error::*;
pub use options::*;

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

#[cfg(all(feature = "std", not(target_family = "wasm")))]
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

#[cfg(not(all(feature = "std", not(target_family = "wasm"))))]
static PAGE_SIZE: &u32 = &4096;

/// Enumeration of possible methods to seek within an [`Allocator`].
#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum ArenaPosition {
  /// Sets the offset to the provided number of bytes.
  Start(u32),

  /// Sets the offset to the capacity of the allocator minus the provided number of bytes.
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

/// The memory chunk allocated from the allocator.
pub trait Buffer {
  /// Returns how many bytes of accessible buffer occupies.
  fn capacity(&self) -> usize;

  /// Returns the accessible offset to the pointer of the allocator.
  fn offset(&self) -> usize;

  /// Returns how many bytes of the whole buffer occupies.
  fn buffer_capacity(&self) -> usize;

  /// Returns the offset to the pointer of the allocator.
  fn buffer_offset(&self) -> usize;

  /// Detach the value from the ARENA, which means when the value is dropped,
  /// the underlying buffer will not be collected for futhur allocation.
  ///
  /// ## Safety
  /// - The caller must ensure the value is dropped before the ARENA is dropped.
  unsafe fn detach(&mut self);

  /// Flush the buffer to the disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush(&self) -> std::io::Result<()>;

  /// Asynchronously flush the buffer to the disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_async(&self) -> std::io::Result<()>;
}

#[inline]
fn write_sanity(freelist: u8, magic_version: u16, data: &mut [u8]) {
  data[FREELIST_OFFSET] = freelist;
  data[MAGIC_TEXT_OFFSET..MAGIC_TEXT_OFFSET + MAGIC_TEXT_SIZE].copy_from_slice(MAGIC_TEXT.as_ref());
  data[MAGIC_VERISON_OFFSET..MAGIC_VERISON_OFFSET + MAGIC_VERISON_SIZE]
    .copy_from_slice(magic_version.to_le_bytes().as_ref());
  data[VERSION_OFFSET..VERSION_OFFSET + VERSION_SIZE]
    .copy_from_slice(CURRENT_VERSION.to_le_bytes().as_ref());
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn sanity_check(
  freelist: Option<Freelist>,
  magic_version: u16,
  data: &[u8],
) -> std::io::Result<Freelist> {
  let stored_freelist = data[FREELIST_OFFSET];
  let stored_freelist = Freelist::try_from(stored_freelist).map_err(invalid_data)?;

  if let Some(freelist) = freelist {
    if stored_freelist != freelist {
      return Err(bad_freelist());
    }
  }

  let stored_magic_version: u16 = u16::from_le_bytes(
    data[MAGIC_VERISON_OFFSET..MAGIC_VERISON_OFFSET + MAGIC_VERISON_SIZE]
      .try_into()
      .unwrap(),
  );
  let version: u16 = u16::from_le_bytes(
    data[VERSION_OFFSET..VERSION_OFFSET + VERSION_SIZE]
      .try_into()
      .unwrap(),
  );

  if stored_magic_version != magic_version {
    return Err(invalid_data(MagicVersionMismatch::new(
      magic_version,
      stored_magic_version,
    )));
  }

  if version != CURRENT_VERSION {
    return Err(invalid_data(VersionMismatch::new(CURRENT_VERSION, version)));
  }

  if data[MAGIC_TEXT_OFFSET..MAGIC_TEXT_OFFSET + MAGIC_TEXT_SIZE] != MAGIC_TEXT {
    return Err(bad_magic());
  }
  Ok(stored_freelist)
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn invalid_data<E: std::error::Error + Send + Sync + 'static>(e: E) -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, e)
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn invalid_input<E: Into<std::boxed::Box<dyn std::error::Error + Send + Sync>>>(
  e: E,
) -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidInput, e)
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn range_out_of_bounds(offset: usize, len: usize, cap: usize) -> std::io::Error {
  #[derive(Debug)]
  struct Err {
    offset: usize,
    len: usize,
    cap: usize,
  }

  impl std::fmt::Display for Err {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      write!(
        f,
        "range [{}..{}] out of bounds (cap={})",
        self.offset, self.len, self.cap
      )
    }
  }

  impl std::error::Error for Err {}

  std::io::Error::new(std::io::ErrorKind::InvalidInput, Err { offset, len, cap })
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
/// ## Examples
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
pub const fn align_offset<T>(current_offset: u32) -> u32 {
  let alignment = core::mem::align_of::<T>() as u32;
  (current_offset + alignment - 1) & !(alignment - 1)
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
      pub fn $name(&mut self, value: $ty) -> Result<(), InsufficientBuffer> {
        const SIZE: usize = core::mem::size_of::<$ty>();

        if self.len + SIZE > self.capacity() {
          return Err(InsufficientBuffer::with_information(SIZE as u64, (self.capacity() - self.len) as u64));
        }

        // SAFETY: We have checked the buffer size.
        unsafe { self. [< $name _unchecked >](value); }
        Ok(())
      }

      #[doc = "Put a `" $ty "` value into the buffer in " $endian " byte order, without doing bounds checking."]
      ///
      #[doc = "For a safe alternative see [`" $name "`](Self::" $name ")."]
      ///
      /// ## Safety
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

#[cfg(feature = "std")]
macro_rules! write_varint {
  ($write_name:ident::$put_name:ident($ty:ident)) => {
    paste::paste! {
      #[doc = "Write a `" $ty "` value into the buffer in LEB128 format, return number of bytes written on success, or an error if the buffer does not have enough space."]
      #[inline]
      #[cfg(feature = "std")]
      pub fn $write_name(&mut self, value: $ty) -> std::io::Result<usize> {
        self.$put_name(value).map_err(|e| std::io::Error::new(std::io::ErrorKind::WriteZero, e))
      }
    }
  }
}

macro_rules! put_varint {
  ($name:ident($ty:ident)) => {
    paste::paste! {
      #[doc = "Put a `" $ty "` value into the buffer in LEB128 format, return an error if the buffer does not have enough space."]
      ///
      /// Returns the number of bytes written.
      #[inline]
      pub fn $name(&mut self, value: $ty) -> Result<usize, dbutils::error::InsufficientBuffer> {
        let buf = unsafe {
          core::slice::from_raw_parts_mut(self.as_mut_ptr().add(self.len), self.capacity() - self.len)
        };
        dbutils::leb128::[< encode_ $ty _varint_to >](value, buf)
          .inspect(|len| self.len += *len)
          .map_err(Into::into)
      }

      #[doc = "Put a `" $ty "` value into the buffer in LEB128 format, without doing error checking."]
      ///
      /// Returns the number of bytes written.
      ///
      /// # Panics
      ///
      #[doc = "- If the buffer does not have enough space to hold the `" $ty "`."]
      #[inline]
      pub fn [< $name _unchecked >] (&mut self, value: $ty) -> usize {
        let buf = unsafe {
          core::slice::from_raw_parts_mut(self.as_mut_ptr().add(self.len), self.capacity() - self.len)
        };
        dbutils::leb128::[< encode_ $ty _varint_to >] (value, buf).inspect(|len| self.len += *len).unwrap()
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
    pub fn align_to<T>(&mut self) -> Result<core::ptr::NonNull<T>, InsufficientBuffer> {
      if mem::size_of::<T>() == 0 {
        return Ok(core::ptr::NonNull::dangling());
      }

      let align_offset = crate::align_offset::<T>(self.allocated.memory_offset + self.len as u32);

      if align_offset > self.allocated.memory_offset + self.allocated.memory_size {
        return Err(InsufficientBuffer::with_information((align_offset as u64 - self.len as u64 - self.allocated.memory_offset as u64), (self.allocated.memory_size as u64 - self.len as u64)));
      }

      self.len = (align_offset - self.allocated.memory_offset) as usize;
      // SAFETY: We have checked the buffer size, and apply the align
      Ok(unsafe {
        core::ptr::NonNull::new_unchecked(self.as_mut_ptr().add(self.len).cast::<T>())
      })
    }

    /// Set the buffer length.
    ///
    /// # Panics
    /// - If `len` is greater than the capacity of the buffer.
    #[inline]
    pub fn set_len(&mut self, len: usize) {
      if len > self.capacity() {
        panic!("length out of bounds");
      }

      if len == self.len {
        return;
      }

      let olen = self.len;
      self.len = len;
      if len > olen {
        unsafe { core::ptr::write_bytes(self.as_mut_ptr().add(olen), 0, len - olen) };
      } else {
        unsafe { core::ptr::write_bytes(self.as_mut_ptr().add(len), 0, olen - len) };
      }
    }

    /// Put `T` into the buffer, return an error if the buffer does not have enough space.
    ///
    /// You may want to use `put_aligned` instead of this method.
    ///
    /// ## Safety
    ///
    /// - Must invoke `align_to` before invoking this method, if `T` is not ZST.
    /// - If `T` needs to be dropped and callers invoke [`detach`](crate::Buffer::detach),
    ///   then the caller must ensure that the `T` is dropped before the allocator is dropped.
    ///   Otherwise, it will lead to memory leaks.
    ///
    /// - If this is file backed allocator, then `T` must be recoverable from bytes.
    ///   1. Types require allocation are not recoverable.
    ///   2. Pointers are not recoverable, like `*const T`, `*mut T`, `NonNull` and any structs contains pointers,
    ///      although those types are on stack, but they cannot be recovered, when reopens the file.
    pub unsafe fn put<T>(&mut self, val: T) -> Result<&mut T, InsufficientBuffer> { unsafe {
      let size = core::mem::size_of::<T>();

      if self.len + size > self.capacity() {
        return Err(InsufficientBuffer::with_information(size as u64, (self.capacity() - self.len) as u64));
      }

      // SAFETY: We have checked the buffer size.
      let ptr = self.as_mut_ptr().add(self.len).cast::<T>();
      ptr.write(val);
      self.len += size;
      Ok(&mut *ptr)
    }}

    /// Put `T` into the buffer, return an error if the buffer does not have enough space.
    ///
    /// ## Safety
    ///
    /// - If `T` needs to be dropped and callers invoke [`RefMut::detach`](crate::RefMut::detach),
    ///   then the caller must ensure that the `T` is dropped before the allocator is dropped.
    ///   Otherwise, it will lead to memory leaks.
    ///
    /// - If this is file backed allocator, then `T` must be recoverable from bytes.
    ///   1. Types require allocation are not recoverable.
    ///   2. Pointers are not recoverable, like `*const T`, `*mut T`, `NonNull` and any structs contains pointers,
    ///      although those types are on stack, but they cannot be recovered, when reopens the file.
    pub unsafe fn put_aligned<T>(&mut self, val: T) -> Result<&mut T, InsufficientBuffer> { unsafe {
      let mut ptr = self.align_to::<T>()?;

      ptr.as_ptr().write(val);
      self.len += ::core::mem::size_of::<T>();
      Ok(ptr.as_mut())
    }}
  };
  (slice) => {
    /// Put a bytes slice into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_slice(&mut self, slice: &[u8]) -> Result<(), InsufficientBuffer> {
      let size = slice.len();

      if self.len + size > self.capacity() {
        return Err(InsufficientBuffer::with_information(size as u64, (self.capacity() - self.len) as u64));
      }

      // SAFETY: We have checked the buffer size.
      unsafe { self.put_slice_unchecked(slice); }
      Ok(())
    }

    /// Put a bytes slice into the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`put_slice`](Self::put_slice).
    ///
    /// ## Safety
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
  (leb($($ty:ident), +$(,)?)) => {
    $(
      paste::paste! {
        put_varint!([< put_ $ty _varint>]($ty));
        #[cfg(feature="std")]
        write_varint!([< write_ $ty _varint>]::[< put_ $ty _varint>]($ty));
      }
    )*
  };
  (8) => {
    /// Put a `u8` value into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_u8(&mut self, value: u8) -> Result<(), InsufficientBuffer> {
      const SIZE: usize = core::mem::size_of::<u8>();

      if self.len + SIZE > self.capacity() {
        return Err(InsufficientBuffer::with_information(SIZE as u64, (self.capacity() - self.len) as u64));
      }

      // SAFETY: We have checked the buffer size.
      unsafe { self.put_u8_unchecked(value); }
      Ok(())
    }

    /// Put a `u8` value into the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`put_u8`](Self::put_u8).
    ///
    /// ## Safety
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
    pub fn put_i8(&mut self, value: i8) -> Result<(), InsufficientBuffer> {
      self.put_u8(value as u8)
    }

    /// Put a `i8` value into the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`put_i8`](Self::put_i8).
    ///
    /// ## Safety
    ///
    /// Calling this method if the buffer does not have enough space to hold the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn put_i8_unchecked(&mut self, value: i8) { unsafe {
      self.put_u8_unchecked(value as u8)
    }}
  };
}

macro_rules! get_byte_order {
  ($name:ident::$converter:ident($ty:ident, $endian:literal)) => {
    paste::paste! {
      #[doc = "Get a `" $ty "` value from the buffer in " $endian " byte order, return an error if the buffer does not have enough bytes."]
      #[inline]
      pub fn $name(&mut self) -> Result<$ty, IncompleteBuffer> {
        const SIZE: usize = core::mem::size_of::<$ty>();

        if self.len < SIZE {
          return Err(IncompleteBuffer::with_information(SIZE as u64, self.len as u64));
        }

        // SAFETY: We have checked the buffer size.
        unsafe { Ok(self.[< $name _unchecked >]()) }
      }

      #[doc = "Get a `" $ty "` value from the buffer in " $endian " byte order, without doing bounds checking."]
      ///
      #[doc = "For a safe alternative see [`" $name "`](Self::" $name ")."]
      ///
      /// ## Safety
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

macro_rules! get_varint {
  ($name:ident($ty:ident)) => {
    paste::paste! {
      #[doc = "Get a `" $ty "` value from the buffer in LEB128 format, return an error if the buffer does not have a valid LEB128 format `" $ty "`."]
      ///
      /// # Returns
      ///
      /// - The first element of the tuple is the number of bytes read from the buffer.
      /// - The second element of the tuple is the decoded value.
      #[doc = "- The second element of the tuple is the decoded `" $ty "`."]
      #[inline]
      pub fn $name(&self) -> Result<(usize, $ty), dbutils::leb128::DecodeVarintError> {
        dbutils::leb128::[< decode_ $ty _varint >](self)
          .map(|(bytes, value)| (bytes, value as $ty))
      }

      #[doc = "Get a `" $ty "` value from the buffer in LEB128 format, without doing checking."]
      ///
      #[doc = "For a safe alternative see [`" $name "`](Self::" $name ")."]
      ///
      /// # Panics
      ///
      #[doc = "- If the buffer does not have a valid LEB128 format `" $ty "`."]
      #[inline]
      pub fn [< $name _unchecked >](&mut self) -> (usize, $ty) {
        dbutils::leb128::[< decode_ $ty _varint >](self)
          .map(|(bytes, value)| (bytes, value as $ty))
          .unwrap()
      }
    }
  }
}

macro_rules! impl_bytes_utils {
  (slice) => {
    /// Get a byte slice from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_slice(&self, size: usize) -> Result<&[u8], IncompleteBuffer> {
      if self.len < size {
        return Err(IncompleteBuffer::with_information(size as u64, self.len as u64));
      }

      // SAFETY: We have checked the buffer size.
      unsafe { Ok(self.get_slice_unchecked(size)) }
    }

    /// Get a byte slice from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_slice`](Self::get_slice).
    ///
    /// ## Safety
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
    pub fn get_slice_mut(&mut self, size: usize) -> Result<&mut [u8], IncompleteBuffer> {
      if self.len < size {
        return Err(IncompleteBuffer::with_information(size as u64, self.len as u64));
      }

      // SAFETY: We have checked the buffer size.
      unsafe { Ok(self.get_slice_mut_unchecked(size)) }
    }

    /// Get a mutable byte slice from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_slice_mut`](Self::get_slice_mut).
    ///
    /// ## Safety
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
  (leb($($ty:ident), +$(,)?)) => {
    $(
      paste::paste! {
        get_varint!([< get_ $ty _varint >]($ty));
      }
    )*
  };
  (8) => {
    /// Get a `u8` value from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_u8(&mut self) -> Result<u8, IncompleteBuffer> {
      if self.len < 1 {
        return Err(IncompleteBuffer::with_information(1, self.len as u64));
      }

      // SAFETY: We have checked the buffer size.
      unsafe { Ok(self.get_u8_unchecked()) }
    }

    /// Get a `u8` value from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_u8`](Self::get_u8).
    ///
    /// ## Safety
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
    pub fn get_i8(&mut self) -> Result<i8, IncompleteBuffer> {
      self.get_u8().map(|v| v as i8)
    }

    /// Get a `i8` value from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_i8`](Self::get_i8).
    ///
    /// ## Safety
    ///
    /// Calling this method if the buffer does not have enough bytes to read the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_i8_unchecked(&mut self) -> i8 { unsafe {
      self.get_u8_unchecked() as i8
    }}
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
  ($ident: ident<A>) => {
    #[cfg(feature = "std")]
    impl<A: $crate::Allocator> std::io::Write for $ident<A> {
      impl_write_in!();
    }
  };
  ($ident: ident<'a, A>) => {
    #[cfg(feature = "std")]
    impl<A: $crate::Allocator> std::io::Write for $ident<'_, A> {
      impl_write_in!();
    }
  };
}

/// The metadata of the structs allocated from ARENA.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Meta {
  parent_ptr: *const u8,
  memory_offset: u32,
  memory_size: u32,
  ptr_offset: u32,
  ptr_size: u32,
}

unsafe impl Send for Meta {}
unsafe impl Sync for Meta {}

impl Meta {
  #[inline]
  const fn null(parent_ptr: *const u8) -> Self {
    Self {
      parent_ptr,
      memory_offset: 0,
      memory_size: 0,
      ptr_offset: 0,
      ptr_size: 0,
    }
  }

  #[inline]
  const fn new(parent_ptr: *const u8, memory_offset: u32, memory_size: u32) -> Self {
    Self {
      parent_ptr,
      memory_offset,
      memory_size,
      // just set the ptr_offset to the memory_offset, and ptr_size to the memory_size.
      // we will align the ptr_offset and ptr_size when it should be aligned.
      ptr_offset: memory_offset,
      ptr_size: memory_size,
    }
  }

  #[inline]
  unsafe fn clear<A: Allocator>(&self, arena: &A) {
    unsafe {
      let ptr = arena.raw_mut_ptr().add(self.ptr_offset as usize);
      core::ptr::write_bytes(ptr, 0, self.ptr_size as usize);
    }
  }

  #[inline]
  fn align_to<T>(&mut self) {
    let align_offset = align_offset::<T>(self.memory_offset);
    self.ptr_offset = align_offset;
    self.ptr_size = mem::size_of::<T>() as u32;
  }

  #[inline]
  fn align_bytes_to<T>(&mut self) {
    let align_offset = align_offset::<T>(self.memory_offset);
    self.ptr_offset = align_offset;
    self.ptr_size = self.memory_offset + self.memory_size - self.ptr_offset;
  }
}

mod bytes;
pub use bytes::*;

mod object;
pub use object::*;

/// Lock-free allocator allocator can be used in concurrent environments.
pub mod sync;

/// allocator allocator for single-threaded environments.
pub mod unsync;
