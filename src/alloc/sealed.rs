use super::*;

pub trait Sealed {}

impl Sealed for u16 {}
impl Sealed for u32 {}
impl Sealed for u64 {}

#[doc(hidden)]
pub trait Atomic<T>: fmt::Debug {
  fn new(value: T) -> Self;
  fn load(&self, order: Ordering) -> T;
  fn store(&self, val: T, order: Ordering);
  fn fetch_add(&self, val: T, order: Ordering) -> T;
  fn compare_exchange_weak(
    &self,
    current: T,
    new: T,
    success: Ordering,
    failure: Ordering,
  ) -> Result<T, T>;
}

macro_rules! impl_atomic {
  ($($ty: ident), +$(,)?) => {
    $(
      paste::paste! {
        impl Atomic<$ty> for [< Atomic $ty: camel>] {
          #[inline]
          fn new(value: $ty) -> Self {
            [< Atomic $ty: camel>]::new(value)
          }

          #[inline]
          fn load(&self, order: Ordering) -> $ty {
            self.load(order)
          }

          #[inline]
          fn store(&self, val: $ty, order: Ordering) {
            self.store(val, order);
          }

          #[inline]
          fn fetch_add(&self, val: $ty, order: Ordering) -> $ty {
            self.fetch_add(val, order)
          }

          #[inline]
          fn compare_exchange_weak(
            &self,
            current: $ty,
            new: $ty,
            success: Ordering,
            failure: Ordering,
          ) -> Result<$ty, $ty> {
            self.compare_exchange_weak(current, new, success, failure)
          }
        }
      }
    )*
  };
}

impl_atomic!(u16, u32, u64);
