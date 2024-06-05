use super::*;

#[derive(Debug)]
enum Kind<T> {
  Slot(MaybeUninit<T>),
  Inline(NonNull<T>),
  /// zero-sized type
  Dangling(NonNull<T>),
}

/// A mutable reference to a value `T` in the ARENA.
#[derive(Debug)]
#[must_use = "The `T` is uninitialized, and must be initialized by `write` before it is used, if `T` is not zero sized type."]
pub struct RefMut<'a, T> {
  kind: Kind<T>,
  arena: &'a Arena,
  detached: bool,
  offset: u32,
  size: usize,
}

impl<'a, T> RefMut<'a, T> {
  /// Detach the value from the ARENA, which means when the value is dropped,
  /// the underlying memory will not be collected for futhur allocation.
  ///
  /// # Safety
  /// - If `T` is not inlined ([`core::mem::needs_drop::<T>()`](core::mem::needs_drop) returns `true`), then users should take care of dropping the value by themselves.
  #[inline]
  pub unsafe fn detach(&mut self) {
    self.detached = true;
  }

  /// Write a value to the `RefMut`.
  #[inline]
  pub fn write(&mut self, value: T) {
    match &mut self.kind {
      Kind::Slot(slot) => unsafe {
        slot.as_mut_ptr().write(value);
      },
      Kind::Inline(ptr) => unsafe {
        ptr.as_ptr().write(value);
      },
      Kind::Dangling(_) => {}
    }
  }

  /// Returns the offset to the pointer of the ARENA.
  #[inline]
  pub const fn offset(&self) -> usize {
    self.offset as usize
  }

  /// Returns a shared reference to the value.
  ///
  /// # Safety
  /// - The value must be initialized.
  pub unsafe fn as_ref(&self) -> &T {
    match &self.kind {
      Kind::Slot(slot) => slot.as_ptr().as_ref().unwrap(),
      Kind::Inline(ptr) => ptr.as_ref(),
      Kind::Dangling(val) => val.as_ref(),
    }
  }

  /// Returns a mutable reference to the value.
  ///
  /// # Safety
  /// - The value must be initialized.
  pub unsafe fn as_mut(&mut self) -> &mut T {
    match &mut self.kind {
      Kind::Slot(slot) => slot.as_mut_ptr().as_mut().unwrap(),
      Kind::Inline(ptr) => ptr.as_mut(),
      Kind::Dangling(val) => val.as_mut(),
    }
  }

  /// Returns the pointer to the `T`, the pointer may not be initialized.
  /// If the pointer is not initialized, then [`NonNull::dangling()`] is returned.
  pub fn as_mut_ptr(&mut self) -> NonNull<T> {
    match &mut self.kind {
      Kind::Slot(slot) => {
        if slot.as_ptr().is_null() {
          NonNull::dangling()
        } else {
          // SAFETY: we have checked that the pointer is not null.
          unsafe { NonNull::new_unchecked(slot.as_mut_ptr()) }
        }
      }
      Kind::Inline(ptr) => *ptr,
      Kind::Dangling(val) => *val,
    }
  }

  #[inline]
  pub(super) const fn new(
    slot: MaybeUninit<T>,
    offset: u32,
    size: usize,
    arena: &'a Arena,
  ) -> Self {
    Self {
      kind: Kind::Slot(slot),
      arena,
      detached: false,
      offset,
      size,
    }
  }

  #[inline]
  pub(super) const fn new_inline(
    value: NonNull<T>,
    offset: u32,
    size: usize,
    arena: &'a Arena,
  ) -> Self {
    Self {
      kind: Kind::Inline(value),
      arena,
      offset,
      size,
      detached: false,
    }
  }

  #[inline]
  pub(super) const fn new_zst(arena: &'a Arena) -> Self {
    Self {
      kind: Kind::Dangling(NonNull::dangling()),
      arena,
      detached: false,
      offset: 0,
      size: 0,
    }
  }
}

impl<'a, T> Drop for RefMut<'a, T> {
  fn drop(&mut self) {
    match &mut self.kind {
      Kind::Slot(slot) => {
        if !self.detached {
          unsafe {
            if mem::needs_drop::<T>() {
              let ptr = slot.as_mut_ptr();
              if !ptr.is_null() {
                ptr::drop_in_place(ptr);
              }
            }
          }
          self.arena.dealloc(self.offset, self.size as u32);
        }
      }
      Kind::Inline(_) => {
        if !self.detached {
          self.arena.dealloc(self.offset, self.size as u32);
        }
      }
      Kind::Dangling(_) => {}
    }
  }
}
