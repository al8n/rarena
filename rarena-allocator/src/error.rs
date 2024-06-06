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
}

impl core::fmt::Display for Error {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    match self {
      Error::InsufficientSpace {
        requested,
        available,
      } => write!(
        f,
        "Allocation failed: requested size is {}, but only {} is available",
        requested, available
      ),
      Error::ReadOnly => write!(f, "Arena is read-only"),
    }
  }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {}
