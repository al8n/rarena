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

mod arena;
pub use arena::*;

mod error;
pub use error::*;

mod options;
pub use options::*;

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

mod common {
  #[cfg(not(feature = "loom"))]
  pub(crate) use std::alloc::{alloc_zeroed, dealloc, Layout};

  #[cfg(feature = "loom")]
  pub(crate) use loom::alloc::{alloc_zeroed, dealloc, Layout};

  #[cfg(not(feature = "loom"))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(feature = "loom")]
  pub(crate) use loom::sync::atomic::*;
}
