use either::Either;

use super::*;

/// A owned buffer that allocated by the ARENA
pub struct BytesMut {
  arena: Either<Arena, NonNull<u8>>,
  detach: bool,
  len: usize,
  allocated: Meta,
}

unsafe impl Send for BytesMut {}
unsafe impl Sync for BytesMut {}

impl ops::Deref for BytesMut {
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

impl ops::DerefMut for BytesMut {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Either::Left(ref arena) => unsafe { arena.get_bytes_mut(self.offset(), self.len) },
      Either::Right(_) => &mut [],
    }
  }
}

impl AsRef<[u8]> for BytesMut {
  #[inline]
  fn as_ref(&self) -> &[u8] {
    self
  }
}

impl AsMut<[u8]> for BytesMut {
  #[inline]
  fn as_mut(&mut self) -> &mut [u8] {
    self
  }
}

impl_write!(BytesMut);

impl BytesMut {
  impl_bytes_mut_utils!(8);

  impl_bytes_mut_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);

  impl_bytes_mut_utils!(slice);

  impl_bytes_mut_utils!(align);

  impl_bytes_utils!(8);

  impl_bytes_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);

  impl_bytes_utils!(slice);

  /// Returns the capacity of the buffer, without the padding.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.allocated.ptr_size as usize
  }

  /// Returns the offset to the pointer of the ARENA.
  #[inline]
  pub const fn offset(&self) -> usize {
    self.allocated.ptr_offset as usize
  }

  /// Returns the offset to the pointer of the ARENA. Including the padding.
  #[inline]
  pub const fn memory_offset(&self) -> usize {
    self.allocated.memory_offset as usize
  }

  /// Returns how many bytes of memory the value occupies. Including the padding.
  #[inline]
  pub const fn memory_capacity(&self) -> usize {
    self.allocated.memory_size as usize
  }

  /// Detach the buffer from the ARENA, and the buffer will not be collected by ARENA when dropped,
  /// which means the space used by the buffer will never be reclaimed.
  #[inline]
  pub fn detach(&mut self) {
    self.detach = true;
  }

  /// Returns the pointer to the buffer.
  #[inline]
  pub fn as_mut_ptr(&self) -> *mut u8 {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    match self.arena.as_ref() {
      Either::Left(arena) => unsafe { arena.get_pointer_mut(self.offset()) },
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

  /// Flush the buffer to the disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush(&self) -> std::io::Result<()> {
    match self.arena.as_ref() {
      Either::Left(arena) => arena.flush_range(
        self.allocated.ptr_offset as usize,
        self.allocated.ptr_size as usize,
      ),
      Either::Right(_) => Ok(()),
    }
  }

  /// Asynchronously flush the buffer to the disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush_async(&self) -> std::io::Result<()> {
    match self.arena.as_ref() {
      Either::Left(arena) => arena.flush_async_range(
        self.allocated.ptr_offset as usize,
        self.allocated.ptr_size as usize,
      ),
      Either::Right(_) => Ok(()),
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
  const fn buffer(&self) -> &[u8] {
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Either::Left(ref arena) => unsafe { arena.get_bytes(self.offset(), self.capacity()) },
      Either::Right(_) => &[],
    }
  }

  #[inline]
  fn buffer_mut(&mut self) -> &mut [u8] {
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Either::Left(ref arena) => unsafe { arena.get_bytes_mut(self.offset(), self.capacity()) },
      Either::Right(_) => &mut [],
    }
  }
}

impl Drop for BytesMut {
  #[inline]
  fn drop(&mut self) {
    match self.arena {
      Either::Left(_) if self.detach => {}
      // SAFETY: offset and offset + size are inbounds of the ARENA.
      Either::Left(ref arena) => unsafe {
        let _ = arena.dealloc(self.allocated.memory_offset, self.allocated.memory_size);
      },
      Either::Right(_) => {}
    }
  }
}

/// A buffer that allocated by the ARENA
pub struct BytesRefMut<'a> {
  arena: &'a Arena,
  len: usize,
  pub(super) allocated: Meta,
  pub(super) detach: bool,
}

impl<'a> ops::Deref for BytesRefMut<'a> {
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

impl<'a> ops::DerefMut for BytesRefMut<'a> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    if self.allocated.ptr_size == 0 {
      return &mut [];
    }

    // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
    unsafe { self.arena.get_bytes_mut(self.offset(), self.len) }
  }
}

impl<'a> AsRef<[u8]> for BytesRefMut<'a> {
  #[inline]
  fn as_ref(&self) -> &[u8] {
    self
  }
}

impl<'a> AsMut<[u8]> for BytesRefMut<'a> {
  #[inline]
  fn as_mut(&mut self) -> &mut [u8] {
    self
  }
}

impl_write!(BytesRefMut<'a>);

impl<'a> BytesRefMut<'a> {
  impl_bytes_mut_utils!(8);

  impl_bytes_mut_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);

  impl_bytes_mut_utils!(slice);

  impl_bytes_mut_utils!(align);

  impl_bytes_utils!(8);

  impl_bytes_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);

  impl_bytes_utils!(slice);

  /// Returns the capacity of the buffer, without the padding.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.allocated.ptr_size as usize
  }

  /// Returns the offset to the pointer of the ARENA.
  #[inline]
  pub const fn offset(&self) -> usize {
    self.allocated.ptr_offset as usize
  }

  /// Returns the offset to the pointer of the ARENA. Including the padding.
  #[inline]
  pub const fn memory_offset(&self) -> usize {
    self.allocated.memory_offset as usize
  }

  /// Returns how many bytes of memory the value occupies. Including the padding.
  #[inline]
  pub const fn memory_capacity(&self) -> usize {
    self.allocated.memory_size as usize
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

  /// Detach the buffer from the ARENA, and the buffer will not be collected by ARENA when dropped,
  /// which means the space used by the buffer will never be reclaimed.
  #[inline]
  pub fn detach(&mut self) {
    self.detach = true;
  }

  /// Returns the pointer to the buffer.
  #[inline]
  pub fn as_mut_ptr(&self) -> *mut u8 {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    unsafe { self.arena.get_pointer_mut(self.offset()) }
  }

  /// Returns the pointer to the buffer.
  #[inline]
  pub fn as_ptr(&self) -> *const u8 {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    unsafe { self.arena.get_pointer(self.offset()) }
  }

  /// Flush the buffer to the disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush(&self) -> std::io::Result<()> {
    self.arena.flush_range(
      self.allocated.ptr_offset as usize,
      self.allocated.ptr_size as usize,
    )
  }

  /// Asynchronously flush the buffer to the disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn flush_async(&self) -> std::io::Result<()> {
    self.arena.flush_async_range(
      self.allocated.ptr_offset as usize,
      self.allocated.ptr_size as usize,
    )
  }

  /// SAFETY: `len` and `offset` must be valid.
  #[inline]
  pub(super) unsafe fn new(arena: &'a Arena, allocated: Meta) -> Self {
    Self {
      arena,
      len: 0,
      allocated,
      detach: false,
    }
  }

  #[inline]
  pub(super) const fn null(arena: &'a Arena) -> Self {
    Self {
      allocated: Meta::null(arena.ptr as _),
      arena,
      len: 0,
      detach: false,
    }
  }

  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(super) fn to_owned(&mut self) -> BytesMut {
    if self.allocated.memory_size == 0 {
      return BytesMut::null(self.arena.ptr as _);
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
  const fn buffer(&self) -> &[u8] {
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

impl<'a> Drop for BytesRefMut<'a> {
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
