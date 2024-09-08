#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[derive(Debug)]
pub(crate) struct TooSmall {
  cap: usize,
  min_cap: usize,
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl TooSmall {
  #[inline]
  pub(crate) const fn new(cap: usize, min_cap: usize) -> Self {
    Self { cap, min_cap }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl core::fmt::Display for TooSmall {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "memmap size is less than the minimum capacity: {} < {}",
      self.cap, self.min_cap
    )
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl std::error::Error for TooSmall {}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[derive(Debug)]
pub(crate) struct MagicVersionMismatch {
  expected_version: u16,
  found_version: u16,
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl MagicVersionMismatch {
  #[inline]
  pub(crate) const fn new(expected_version: u16, found_version: u16) -> Self {
    Self {
      expected_version,
      found_version,
    }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl core::fmt::Display for MagicVersionMismatch {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "magic version mismatch: expected version {}, but found version {}.",
      self.expected_version, self.found_version
    )
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl std::error::Error for MagicVersionMismatch {}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[derive(Debug)]
pub(crate) struct VersionMismatch {
  expected_version: u16,
  found_version: u16,
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl VersionMismatch {
  #[inline]
  pub(crate) const fn new(expected_version: u16, found_version: u16) -> Self {
    Self {
      expected_version,
      found_version,
    }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl core::fmt::Display for VersionMismatch {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "version mismatch: expected version {}, but found version {}.",
      self.expected_version, self.found_version
    )
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl std::error::Error for VersionMismatch {}

/// Error indicating that the buffer does not have enough space to write bytes into.
#[derive(Debug, Default, Clone, Copy)]
pub struct BufferTooSmall {
  /// The remaining space in the buffer.
  pub(crate) remaining: usize,
  /// The required space to write into the buffer.
  pub(crate) want: usize,
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
  pub(crate) remaining: usize,
  /// The number of bytes required to be read.
  pub(crate) read: usize,
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

/// An error indicating that the arena is full
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum Error {
  /// Insufficient space in the arena
  InsufficientSpace {
    /// The requested size
    requested: u32,
    /// The remaining size
    available: u32,
  },
  /// The arena is read-only
  ReadOnly,

  /// The requested size is larger than the page size
  LargerThanPageSize {
    /// The requested size
    requested: u32,
    /// The page size
    page_size: u32,
  },

  /// Index is out of range
  OutOfBounds {
    /// The offset
    offset: usize,
    /// The current allocated size of the arena
    allocated: usize,
  },

  /// Returned when decoding a LEB128 value fails
  DecodeVarintError(dbutils::leb128::DecodeVarintError),
}

impl From<dbutils::leb128::DecodeVarintError> for Error {
  #[inline]
  fn from(e: dbutils::leb128::DecodeVarintError) -> Self {
    Self::DecodeVarintError(e)
  }
}

impl Error {
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(crate) const fn larger_than_page_size(requested: u32, page_size: u32) -> Self {
    Self::LargerThanPageSize {
      requested,
      page_size,
    }
  }
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Self::InsufficientSpace {
        requested,
        available,
      } => write!(
        f,
        "Allocation failed: requested size is {}, but only {} is available",
        requested, available
      ),
      Self::ReadOnly => write!(f, "Arena is read-only"),
      Self::LargerThanPageSize {
        requested,
        page_size,
      } => write!(
        f,
        "Allocation failed: cannot allocate in the same page, requested size is {}, but the page size is {}",
        requested, page_size
      ),
      Self::OutOfBounds { offset, allocated } => write!(
        f,
        "Index out of bounds: offset {} is out of range, the current allocated size is {}",
        offset, allocated
      ),
      Self::DecodeVarintError(e) => write!(f, "{}", e),
    }
  }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}
