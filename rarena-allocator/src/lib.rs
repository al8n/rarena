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
