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
    let align = align.max(mem::align_of::<H>()).min(8);
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
