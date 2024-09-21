use core::{ops, ptr::NonNull};

pub use dbutils::leb128::{DecodeVarintError, EncodeVarintError};
use either::Either;

use super::*;

/// A owned buffer that allocated by the ARENA
pub struct BytesMut<A: Allocator> {
  arena: Either<A, NonNull<u8>>,
  detach: bool,
  len: usize,
  allocated: Meta,
}

unsafe impl<A: Allocator + Send> Send for BytesMut<A> {}
unsafe impl<A: Allocator + Sync> Sync for BytesMut<A> {}

impl<A: Allocator> ops::Deref for BytesMut<A> {
  type Target = [u8];

  #[inline]
  fn deref(&self) -> &Self::Target {
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Either::Left(ref arena) => unsafe { arena.get_bytes(self.offset(), self.len) },
      Either::Right(_) => &[],
    }
  }
}

impl<A: Allocator> ops::DerefMut for BytesMut<A> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    let offset = self.offset();
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Either::Left(ref mut arena) => unsafe { arena.get_bytes_mut(offset, self.len) },
      Either::Right(_) => &mut [],
    }
  }
}

impl<A: Allocator> AsRef<[u8]> for BytesMut<A> {
  #[inline]
  fn as_ref(&self) -> &[u8] {
    self
  }
}

impl<A: Allocator> AsMut<[u8]> for BytesMut<A> {
  #[inline]
  fn as_mut(&mut self) -> &mut [u8] {
    self
  }
}

impl_write!(BytesMut<A>);

impl<A: Allocator> crate::Buffer for BytesMut<A> {
  #[inline]
  fn capacity(&self) -> usize {
    self.allocated.ptr_size as usize
  }

  #[inline]
  fn offset(&self) -> usize {
    self.allocated.ptr_offset as usize
  }

  #[inline]
  fn buffer_offset(&self) -> usize {
    self.allocated.memory_offset as usize
  }

  #[inline]
  fn buffer_capacity(&self) -> usize {
    self.allocated.memory_size as usize
  }

  #[inline]
  unsafe fn detach(&mut self) {
    self.detach = true;
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush(&self) -> std::io::Result<()> {
    match self.arena.as_ref() {
      Either::Left(arena) => arena.flush_range(
        self.allocated.ptr_offset as usize,
        self.allocated.ptr_size as usize,
      ),
      Either::Right(_) => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_async(&self) -> std::io::Result<()> {
    match self.arena.as_ref() {
      Either::Left(arena) => arena.flush_async_range(
        self.allocated.ptr_offset as usize,
        self.allocated.ptr_size as usize,
      ),
      Either::Right(_) => Ok(()),
    }
  }
}

impl<A: Allocator> BytesMut<A> {
  impl_bytes_mut_utils!(8);
  impl_bytes_mut_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);
  impl_bytes_mut_utils!(leb(u16, u32, u64, u128, i16, i32, i64, i128));
  impl_bytes_mut_utils!(slice);
  impl_bytes_mut_utils!(align);

  impl_bytes_utils!(8);
  impl_bytes_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);
  impl_bytes_utils!(leb(u16, u32, u64, u128, i16, i32, i64, i128));
  impl_bytes_utils!(slice);

  /// Returns the mutable pointer to the buffer.
  #[inline]
  pub fn as_mut_ptr(&mut self) -> *mut u8 {
    let offset = self.offset();
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    match self.arena.as_mut() {
      Either::Left(arena) => unsafe { arena.get_pointer_mut(offset) },
      Either::Right(ptr) => ptr.as_ptr(),
    }
  }

  /// Returns the pointer to the buffer.
  #[inline]
  pub fn as_ptr(&self) -> *const u8 {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    match self.arena.as_ref() {
      Either::Left(arena) => unsafe { arena.get_pointer(self.offset()) },
      Either::Right(ptr) => ptr.as_ptr(),
    }
  }

  #[inline]
  pub(super) fn null(parent_ptr: *const u8) -> Self {
    Self {
      arena: Either::Right(NonNull::dangling()),
      len: 0,
      allocated: Meta::null(parent_ptr),
      detach: false,
    }
  }

  #[inline]
  fn buffer(&self) -> &[u8] {
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Either::Left(ref arena) => unsafe { arena.get_bytes(self.offset(), self.capacity()) },
      Either::Right(_) => &[],
    }
  }

  #[inline]
  fn buffer_mut(&mut self) -> &mut [u8] {
    let offset = self.offset();
    let cap = self.capacity();
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Either::Left(ref mut arena) => unsafe { arena.get_bytes_mut(offset, cap) },
      Either::Right(_) => &mut [],
    }
  }
}

impl<A: Allocator> Drop for BytesMut<A> {
  #[inline]
  fn drop(&mut self) {
    match self.arena {
      Either::Left(_) if self.detach => {}
      // SAFETY: offset and offset + size are inbounds of the ARENA.
      Either::Left(ref mut arena) => unsafe {
        let _ = arena.dealloc(self.allocated.memory_offset, self.allocated.memory_size);
      },
      Either::Right(_) => {}
    }
  }
}

/// A buffer that allocated by the ARENA
pub struct BytesRefMut<'a, A: Allocator> {
  arena: &'a A,
  len: usize,
  pub(super) allocated: Meta,
  pub(super) detach: bool,
}

impl<A: Allocator> ops::Deref for BytesRefMut<'_, A> {
  type Target = [u8];

  #[inline]
  fn deref(&self) -> &Self::Target {
    if self.allocated.ptr_size == 0 {
      return &[];
    }

    // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
    unsafe { self.arena.get_bytes(self.offset(), self.len) }
  }
}

impl<A: Allocator> ops::DerefMut for BytesRefMut<'_, A> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    if self.allocated.ptr_size == 0 {
      return &mut [];
    }

    // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
    unsafe { self.arena.get_bytes_mut(self.offset(), self.len) }
  }
}

impl<A: Allocator> AsRef<[u8]> for BytesRefMut<'_, A> {
  #[inline]
  fn as_ref(&self) -> &[u8] {
    self
  }
}

impl<A: Allocator> AsMut<[u8]> for BytesRefMut<'_, A> {
  #[inline]
  fn as_mut(&mut self) -> &mut [u8] {
    self
  }
}

impl_write!(BytesRefMut<'a, A>);

impl<A: Allocator> crate::Buffer for BytesRefMut<'_, A> {
  #[inline]
  fn capacity(&self) -> usize {
    self.allocated.ptr_size as usize
  }

  #[inline]
  fn offset(&self) -> usize {
    self.allocated.ptr_offset as usize
  }

  #[inline]
  fn buffer_offset(&self) -> usize {
    self.allocated.memory_offset as usize
  }

  #[inline]
  fn buffer_capacity(&self) -> usize {
    self.allocated.memory_size as usize
  }

  #[inline]
  unsafe fn detach(&mut self) {
    self.detach = true;
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush(&self) -> std::io::Result<()> {
    self.arena.flush_range(
      self.allocated.ptr_offset as usize,
      self.allocated.ptr_size as usize,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_async(&self) -> std::io::Result<()> {
    self.arena.flush_async_range(
      self.allocated.ptr_offset as usize,
      self.allocated.ptr_size as usize,
    )
  }
}

impl<'a, A: Allocator> BytesRefMut<'a, A> {
  impl_bytes_mut_utils!(8);
  impl_bytes_mut_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);
  impl_bytes_mut_utils!(leb(u16, u32, u64, u128, i16, i32, i64, i128));
  impl_bytes_mut_utils!(slice);
  impl_bytes_mut_utils!(align);

  impl_bytes_utils!(8);
  impl_bytes_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);
  impl_bytes_utils!(leb(u16, u32, u64, u128, i16, i32, i64, i128));
  impl_bytes_utils!(slice);

  /// Returns the mutable pointer to the buffer.
  #[inline]
  pub fn as_mut_ptr(&mut self) -> *mut u8 {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    unsafe { self.arena.get_pointer_mut(self.offset()) }
  }

  /// Returns the pointer to the buffer.
  #[inline]
  pub fn as_ptr(&self) -> *const u8 {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    unsafe { self.arena.get_pointer(self.offset()) }
  }

  /// Returns the length of the buffer.
  #[inline]
  pub const fn len(&self) -> usize {
    self.len
  }

  /// Returns `true` if the buffer is empty.
  #[inline]
  pub const fn is_empty(&self) -> bool {
    self.len == 0
  }

  /// Returns the remaining capacity.
  #[inline]
  pub const fn remaining(&self) -> usize {
    self.allocated.ptr_size as usize - self.len
  }

  /// SAFETY: `len` and `offset` must be valid.
  #[inline]
  pub(super) unsafe fn new(arena: &'a A, allocated: Meta) -> Self {
    Self {
      arena,
      len: 0,
      allocated,
      detach: false,
    }
  }

  #[inline]
  pub(super) fn null(arena: &'a A) -> Self {
    Self {
      allocated: Meta::null(arena.raw_ptr() as _),
      arena,
      len: 0,
      detach: false,
    }
  }

  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(super) fn to_owned(&mut self) -> BytesMut<A> {
    if self.allocated.memory_size == 0 {
      return BytesMut::null(self.arena.raw_ptr() as _);
    }
    self.detach = true;

    BytesMut {
      arena: Either::Left(self.arena.clone()),
      len: self.len,
      allocated: self.allocated,
      detach: false,
    }
  }

  #[inline]
  fn buffer(&self) -> &[u8] {
    if self.allocated.ptr_size == 0 {
      return &[];
    }

    // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
    unsafe { self.arena.get_bytes(self.offset(), self.capacity()) }
  }

  #[inline]
  fn buffer_mut(&mut self) -> &mut [u8] {
    if self.allocated.ptr_size == 0 {
      return &mut [];
    }

    // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
    unsafe { self.arena.get_bytes_mut(self.offset(), self.capacity()) }
  }
}

impl<A: Allocator> Drop for BytesRefMut<'_, A> {
  #[inline]
  fn drop(&mut self) {
    if self.detach {
      return;
    }

    // SAFETY: offset and offset + size are inbounds of the ARENA.
    unsafe {
      self
        .arena
        .dealloc(self.allocated.memory_offset, self.allocated.memory_size);
    }
  }
}
