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

/// Lock-free ARENA allocator can be used in concurrent environments.
pub mod sync;

/// ARENA allocator for single-threaded environments.
pub mod unsync;

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
  pub(crate) use std::alloc::{alloc_zeroed, dealloc, Layout};

  #[cfg(feature = "loom")]
  pub(crate) use loom::alloc::{alloc_zeroed, dealloc, Layout};

  #[cfg(not(feature = "loom"))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(feature = "loom")]
  pub(crate) use loom::sync::atomic::*;

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
