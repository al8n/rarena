use super::*;

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

        if self.len + SIZE > self.cap {
          return Err(BufferTooSmall {
            remaining: self.cap - self.len,
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
  (slice) => {
    /// Put a bytes slice into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_slice(&mut self, slice: &[u8]) -> Result<(), BufferTooSmall> {
      let size = slice.len();

      if self.len + size > self.cap {
        return Err(BufferTooSmall {
          remaining: self.cap - self.len,
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
        write_byte_order!([< write_ $ty _be>]::[< put_ $ty _be>]::to_be_bytes($ty, "big-endian"));
        write_byte_order!([< write_ $ty _le >]::[< put_ $ty _le >]::to_le_bytes($ty, "little-endian"));
        write_byte_order!([< write_ $ty _ne >]::[< put_ $ty _ne >]::to_ne_bytes($ty, "native-endian"));
      }
    )*
  };
  (8) => {
    /// Put a `u8` value into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_u8(&mut self, value: u8) -> Result<(), BufferTooSmall> {
      const SIZE: usize = core::mem::size_of::<u8>();

      if self.len + SIZE > self.cap {
        return Err(BufferTooSmall {
          remaining: self.cap - self.len,
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
}

/// Error indicating that the buffer does not have enough space to write bytes into.
#[derive(Debug, Default, Clone, Copy)]
pub struct BufferTooSmall {
  /// The remaining space in the buffer.
  remaining: usize,
  /// The required space to write into the buffer.
  want: usize,
}

impl BufferTooSmall {
  /// Returns the remaining space in the buffer.
  #[inline]
  pub const fn remaining(&self) -> usize {
    self.remaining
  }

  /// Returns the required space to write into the buffer.
  #[inline]
  pub const fn require(&self) -> usize {
    self.want
  }
}

impl core::fmt::Display for BufferTooSmall {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "Buffer does not have enough space (remaining {}, want {})",
      self.remaining, self.want
    )
  }
}

#[cfg(feature = "std")]
impl std::error::Error for BufferTooSmall {}

/// Error indicating that the buffer does not have enough bytes to read from.
#[derive(Debug, Default, Clone, Copy)]
pub struct NotEnoughBytes {
  /// The remaining bytes in the buffer.
  remaining: usize,
  /// The number of bytes required to be read.
  read: usize,
}

impl NotEnoughBytes {
  /// Returns the remaining bytes in the buffer.
  #[inline]
  pub const fn remaining(&self) -> usize {
    self.remaining
  }

  /// Returns the number of bytes required to be read.
  #[inline]
  pub const fn require(&self) -> usize {
    self.read
  }
}

impl core::fmt::Display for NotEnoughBytes {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "Buffer does not have enough bytes to read (remaining {}, want {})",
      self.remaining, self.read
    )
  }
}

#[cfg(feature = "std")]
impl std::error::Error for NotEnoughBytes {}

/// A owned buffer that allocated by the ARENA
pub struct BytesMut {
  arena: Option<Arena>,
  detach: bool,
  len: usize,
  cap: usize,
  offset: usize,
}

impl ops::Deref for BytesMut {
  type Target = [u8];

  #[inline]
  fn deref(&self) -> &Self::Target {
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Some(ref arena) => unsafe { arena.get_bytes(self.offset, self.len) },
      None => &[],
    }
  }
}

impl ops::DerefMut for BytesMut {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Some(ref arena) => unsafe { arena.get_bytes_mut(self.offset, self.len) },
      None => &mut [],
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

  impl_bytes_utils!(8);

  impl_bytes_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);

  impl_bytes_utils!(slice);

  /// Detach the buffer from the ARENA, and the buffer will not be collected by ARENA when dropped,
  /// which means the space used by the buffer will never be reclaimed.
  #[inline]
  pub fn detach(&mut self) {
    self.detach = true;
  }

  #[inline]
  pub(super) fn null() -> Self {
    Self {
      arena: None,
      len: 0,
      cap: 0,
      offset: 0,
      detach: false,
    }
  }

  #[inline]
  const fn buffer(&self) -> &[u8] {
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Some(ref arena) => unsafe { arena.get_bytes(self.offset, self.cap) },
      None => &[],
    }
  }

  #[inline]
  fn buffer_mut(&mut self) -> &mut [u8] {
    match self.arena {
      // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
      Some(ref arena) => unsafe { arena.get_bytes_mut(self.offset, self.cap) },
      None => &mut [],
    }
  }
}

impl Drop for BytesMut {
  #[inline]
  fn drop(&mut self) {
    match self.arena {
      Some(_) if self.detach => {}
      Some(ref arena) => arena.dealloc(self.offset, self.cap, self.len),
      None => {}
    }
  }
}

/// A buffer that allocated by the ARENA
pub struct BytesRefMut<'a> {
  arena: &'a Arena,
  len: usize,
  pub(super) cap: usize,
  pub(super) offset: usize,
  pub(super) detach: bool,
}

impl<'a> ops::Deref for BytesRefMut<'a> {
  type Target = [u8];

  #[inline]
  fn deref(&self) -> &Self::Target {
    if self.cap == 0 {
      return &[];
    }

    // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
    unsafe { self.arena.get_bytes(self.offset, self.len) }
  }
}

impl<'a> ops::DerefMut for BytesRefMut<'a> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    if self.cap == 0 {
      return &mut [];
    }

    // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
    unsafe { self.arena.get_bytes_mut(self.offset, self.len) }
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

  impl_bytes_utils!(8);

  impl_bytes_utils!(u16, u32, u64, usize, u128, i16, i32, i64, isize, i128);

  impl_bytes_utils!(slice);

  /// Returns the capacity of the buffer.
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.cap
  }

  /// Detach the buffer from the ARENA, and the buffer will not be collected by ARENA when dropped,
  /// which means the space used by the buffer will never be reclaimed.
  #[inline]
  pub fn detach(&mut self) {
    self.detach = true;
  }

  /// SAFETY: `len` and `offset` must be valid.
  #[inline]
  pub(super) unsafe fn new(arena: &'a Arena, len: u32, offset: u32) -> Self {
    Self {
      arena,
      len: 0,
      cap: len as usize,
      offset: offset as usize,
      detach: false,
    }
  }

  #[inline]
  pub(super) const fn null(arena: &'a Arena) -> Self {
    Self {
      arena,
      cap: 0,
      len: 0,
      offset: 0,
      detach: false,
    }
  }

  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(super) fn to_owned(&mut self) -> BytesMut {
    if self.cap == 0 {
      return BytesMut::null();
    }
    self.detach = true;

    BytesMut {
      arena: Some(self.arena.clone()),
      len: self.len,
      cap: self.cap,
      offset: self.offset,
      detach: false,
    }
  }

  #[inline]
  const fn buffer(&self) -> &[u8] {
    if self.cap == 0 {
      return &[];
    }

    // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
    unsafe { self.arena.get_bytes(self.offset, self.cap) }
  }

  #[inline]
  fn buffer_mut(&mut self) -> &mut [u8] {
    if self.cap == 0 {
      return &mut [];
    }

    // SAFETY: The buffer is allocated by the ARENA, and the len and offset are valid.
    unsafe { self.arena.get_bytes_mut(self.offset, self.cap) }
  }
}

impl<'a> Drop for BytesRefMut<'a> {
  #[inline]
  fn drop(&mut self) {
    if self.detach {
      return;
    }

    self.arena.dealloc(self.offset, self.len, self.cap);
  }
}
