use core::marker::PhantomData;

use super::*;

/// An owned object in the ARENA.
pub struct Owned<T, S: Size> {
  arena: Arena<S>,
  ptr: NonNull<T>,
  arena_offset: usize,
  detach: bool,
  size: usize,
  _marker: PhantomData<T>,
}

impl<T, S: Size> ops::Deref for Owned<T, S> {
  type Target = T;

  #[inline]
  fn deref(&self) -> &Self::Target {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    unsafe { self.ptr.as_ref() }
  }
}

impl<T, S: Size> ops::DerefMut for Owned<T, S> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    unsafe { self.ptr.as_mut() }
  }
}

impl<T, S: Size> AsRef<T> for Owned<T, S> {
  #[inline]
  fn as_ref(&self) -> &T {
    self
  }
}

impl<T, S: Size> AsMut<T> for Owned<T, S> {
  #[inline]
  fn as_mut(&mut self) -> &mut T {
    self
  }
}

impl<T, S: Size> Owned<T, S> {
  /// Detach the buffer from the ARENA, and the buffer will not be collected by ARENA when dropped,
  /// which means the space used by the buffer will never be reclaimed.
  #[inline]
  pub fn detach(&mut self) {
    self.detach = true;
  }
}

impl<T, S: Size> Drop for Owned<T, S> {
  #[inline]
  fn drop(&mut self) {
    if self.detach {
      return;
    }

    self.arena.dealloc(self.arena_offset, self.size, self.size);
  }
}

/// A reference to an object in the ARENA.
pub struct RefMut<'a, T, S: Size> {
  arena: &'a Arena<S>,
  ptr: NonNull<T>,
  arena_offset: usize,
  /// the size of allocated buffer
  size: usize,
  detach: bool,
  _marker: PhantomData<T>,
}

impl<'a, T, S: Size> ops::Deref for RefMut<'a, T, S> {
  type Target = T;

  #[inline]
  fn deref(&self) -> &Self::Target {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    unsafe { self.ptr.as_ref() }
  }
}

impl<'a, T, S: Size> ops::DerefMut for RefMut<'a, T, S> {
  #[inline]
  fn deref_mut(&mut self) -> &mut Self::Target {
    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    unsafe { self.ptr.as_mut() }
  }
}

impl<'a, T, S: Size> AsRef<T> for RefMut<'a, T, S> {
  #[inline]
  fn as_ref(&self) -> &T {
    self
  }
}

impl<'a, T, S: Size> AsMut<T> for RefMut<'a, T, S> {
  #[inline]
  fn as_mut(&mut self) -> &mut T {
    self
  }
}

impl<'a, T, S: Size> RefMut<'a, T, S> {
  /// Detach the buffer from the ARENA, and the buffer will not be collected by ARENA when dropped,
  /// which means the space used by the buffer will never be reclaimed.
  #[inline]
  pub fn detach(&mut self) {
    self.detach = true;
  }

  #[inline]
  pub(super) fn new(
    arena: &'a Arena<S>,
    ptr: NonNull<T>,
    arena_offset: usize,
    size: usize,
  ) -> Self {
    Self {
      arena,
      ptr,
      arena_offset,
      size,
      detach: false,
      _marker: PhantomData,
    }
  }

  /// SAFETY: `T` must be zero-sized type.
  #[inline]
  pub(super) unsafe fn null(arena: &'a Arena<S>) -> Self {
    Self {
      arena,
      ptr: NonNull::dangling(),
      arena_offset: 0,
      detach: false,
      size: 0,
      _marker: PhantomData,
    }
  }

  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(super) fn to_owned(&mut self) -> Owned<T, S> {
    self.detach = true;

    Owned {
      arena: self.arena.clone(),
      ptr: self.ptr,
      arena_offset: self.arena_offset,
      detach: false,
      size: self.size,
      _marker: PhantomData,
    }
  }
}

impl<'a, T, S: Size> Drop for RefMut<'a, T, S> {
  #[inline]
  fn drop(&mut self) {
    if self.detach {
      return;
    }

    // SAFETY: The buffer is allocated by the ARENA, and the offset is valid.
    self.arena.dealloc(self.arena_offset, self.size, self.size);
  }
}
