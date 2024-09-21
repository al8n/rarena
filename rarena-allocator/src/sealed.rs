use super::common::{AtomicUsize, Ordering, UnsafeCell, UnsafeCellExt};

pub trait RefCounter {
  fn new(val: usize) -> Self;

  fn fetch_add(&self, val: usize, ordering: Ordering) -> usize;

  fn fetch_sub(&self, val: usize, ordering: Ordering) -> usize;
}

impl RefCounter for AtomicUsize {
  fn new(val: usize) -> Self {
    AtomicUsize::new(val)
  }

  fn fetch_add(&self, val: usize, ordering: Ordering) -> usize {
    self.fetch_add(val, ordering)
  }

  fn fetch_sub(&self, val: usize, ordering: Ordering) -> usize {
    self.fetch_sub(val, ordering)
  }
}

impl RefCounter for UnsafeCell<usize> {
  fn new(val: usize) -> Self {
    UnsafeCell::new(val)
  }

  fn fetch_add(&self, value: usize, _ordering: Ordering) -> usize {
    let val = &mut *self.as_inner_ref_mut();
    let old = *val;
    *val += value;
    old
  }

  fn fetch_sub(&self, value: usize, _ordering: Ordering) -> usize {
    let val = &mut *self.as_inner_ref_mut();
    let old = *val;
    *val -= value;
    old
  }
}

pub trait PathRefCounter: Clone {
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn new(path: std::path::PathBuf) -> Self;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn as_path(&self) -> &std::path::Path;
}

#[cfg(not(feature = "std"))]
impl<T> PathRefCounter for std::sync::Arc<T> {}

#[cfg(feature = "std")]
impl PathRefCounter for std::sync::Arc<std::path::PathBuf> {
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn new(path: std::path::PathBuf) -> Self {
    std::sync::Arc::new(path)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn as_path(&self) -> &std::path::Path {
    self
  }
}

#[cfg(feature = "std")]
impl PathRefCounter for std::rc::Rc<std::path::PathBuf> {
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn new(path: std::path::PathBuf) -> Self {
    std::rc::Rc::new(path)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn as_path(&self) -> &std::path::Path {
    self
  }
}

#[cfg(not(feature = "std"))]
impl<T> PathRefCounter for std::rc::Rc<T> {}

pub trait Header: Sized {
  fn new(size: u32, min_segment_size: u32) -> Self;

  fn load_min_segment_size(&self) -> u32;

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn load_allocated(&self) -> u32;
}

/// Sealed trait to prevent users from implementing the trait, so allowing the clippy warning here is okay.
#[allow(private_bounds)]
pub trait Sealed:
  Sized + Clone + From<super::memory::Memory<Self::RefCounter, Self::PathRefCounter, Self::Header>>
{
  type PathRefCounter: PathRefCounter;
  type RefCounter: RefCounter;
  type Header: Header;
}
