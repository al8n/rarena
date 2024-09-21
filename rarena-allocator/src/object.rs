use core::{
  mem::MaybeUninit,
  ptr::{self, NonNull},
};

use super::*;

#[derive(Debug)]
enum Kind<T> {
  Slot(MaybeUninit<T>),
  Inline(NonNull<T>),
  /// zero-sized type
  Dangling(NonNull<T>),
}

impl<T> Default for Kind<T> {
  fn default() -> Self {
    if mem::size_of::<T>() == 0 {
      Kind::Dangling(NonNull::dangling())
    } else if mem::needs_drop::<T>() {
      Kind::Slot(MaybeUninit::uninit())
    } else {
      Kind::Inline(NonNull::dangling())
    }
  }
}

/// An owned to a value `T` in the ARENA.
#[derive(Debug)]
#[must_use = "The `T` is uninitialized, and must be initialized by `write` before it is used, if `T` is not zero sized type."]
pub struct Owned<T, A: Allocator> {
  kind: Kind<T>,
  arena: A,
  detached: bool,
  pub(super) allocated: Meta,
}

unsafe impl<A: Allocator + Send, T> Send for Owned<T, A> {}
unsafe impl<A: Allocator + Sync, T> Sync for Owned<T, A> {}

impl<T, A: Allocator> crate::Buffer for Owned<T, A> {
  /// Returns how many bytes of `T` occupies.
  ///
  /// If this value is `0`, then the `T` is ZST (zero sized type).
  #[inline]
  fn capacity(&self) -> usize {
    self.allocated.ptr_size as usize
  }

  /// Returns the offset of `T` to the pointer of the ARENA.
  ///
  /// If this value is `0`, then the `T` is ZST (zero sized type).
  #[inline]
  fn offset(&self) -> usize {
    self.allocated.ptr_offset as usize
  }

  /// Returns how many bytes of buffer the value occupies.
  ///
  /// If this value is `0`, then the `T` is ZST (zero sized type).
  #[inline]
  fn buffer_capacity(&self) -> usize {
    self.allocated.memory_size as usize
  }

  /// Returns the offset to the pointer of the ARENA.
  ///
  /// If this value is `0`, then the `T` is ZST (zero sized type).
  #[inline]
  fn buffer_offset(&self) -> usize {
    self.allocated.memory_offset as usize
  }

  #[inline]
  unsafe fn detach(&mut self) {
    self.detached = true;
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush(&self) -> std::io::Result<()> {
    self.arena.flush_range(
      self.allocated.ptr_offset as usize,
      self.allocated.ptr_size as usize,
    )
  }

  /// Asynchronously flush the buffer to the disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_async(&self) -> std::io::Result<()> {
    self.arena.flush_async_range(
      self.allocated.memory_offset as usize,
      self.allocated.memory_size as usize,
    )
  }
}

impl<T, A: Allocator> Owned<T, A> {
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

  /// Returns a shared reference to the value.
  ///
  /// ## Safety
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
  /// ## Safety
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
}

impl<T, A: Allocator> Drop for Owned<T, A> {
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
          // SAFETY: offset and offset + size are inbounds of the ARENA.
          unsafe {
            self
              .arena
              .dealloc(self.allocated.memory_offset, self.allocated.memory_size);
          }
        }
      }
      Kind::Inline(_) => {
        if !self.detached {
          // SAFETY: offset and offset + size are inbounds of the ARENA.
          unsafe {
            self
              .arena
              .dealloc(self.allocated.memory_offset, self.allocated.memory_size);
          }
        }
      }
      Kind::Dangling(_) => {}
    }
  }
}

/// A mutable reference to a value `T` in the ARENA.
#[derive(Debug)]
#[must_use = "The `T` is uninitialized, and must be initialized by `write` before it is used, if `T` is not zero sized type."]
pub struct RefMut<'a, T, A: Allocator> {
  kind: Kind<T>,
  arena: &'a A,
  detached: bool,
  pub(super) allocated: Meta,
}

impl<T, A: Allocator> crate::Buffer for RefMut<'_, T, A> {
  #[inline]
  fn capacity(&self) -> usize {
    self.allocated.ptr_size as usize
  }

  #[inline]
  fn offset(&self) -> usize {
    self.allocated.ptr_offset as usize
  }

  #[inline]
  fn buffer_capacity(&self) -> usize {
    self.allocated.memory_size as usize
  }

  #[inline]
  fn buffer_offset(&self) -> usize {
    self.allocated.memory_offset as usize
  }

  /// Detach the value from the ARENA, which means when the value is dropped,
  /// the underlying memory will not be collected for futhur allocation.
  ///
  /// ## Safety
  /// - If `T` is not inlined ([`core::mem::needs_drop::<T>()`](core::mem::needs_drop) returns `true`), then users should take care of dropping the value by themselves.
  #[inline]
  unsafe fn detach(&mut self) {
    self.detached = true;
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush(&self) -> std::io::Result<()> {
    self.arena.flush_range(
      self.allocated.ptr_offset as usize,
      self.allocated.ptr_size as usize,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_async(&self) -> std::io::Result<()> {
    self.arena.flush_async_range(
      self.allocated.ptr_offset as usize,
      self.allocated.ptr_size as usize,
    )
  }
}

impl<'a, T, A: Allocator> RefMut<'a, T, A> {
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

  /// Returns a shared reference to the value.
  ///
  /// ## Safety
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
  /// ## Safety
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
  pub(super) fn new(slot: MaybeUninit<T>, allocated: Meta, arena: &'a A) -> Self {
    Self {
      kind: Kind::Slot(slot),
      arena,
      detached: false,
      allocated,
    }
  }

  #[inline]
  pub(super) fn new_inline(value: NonNull<T>, allocated: Meta, arena: &'a A) -> Self {
    Self {
      kind: Kind::Inline(value),
      arena,
      detached: false,
      allocated,
    }
  }

  #[inline]
  pub(super) fn new_zst(arena: &'a A) -> Self {
    Self {
      kind: Kind::Dangling(NonNull::dangling()),
      allocated: Meta::null(arena.raw_ptr() as _),
      arena,
      detached: false,
    }
  }

  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(super) fn to_owned(&mut self) -> Owned<T, A> {
    self.detached = true;

    Owned {
      arena: self.arena.clone(),
      kind: mem::take(&mut self.kind),
      detached: false,
      allocated: self.allocated,
    }
  }
}

impl<T, A: Allocator> Drop for RefMut<'_, T, A> {
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
          // SAFETY: offset and offset + size are inbounds of the ARENA.
          unsafe {
            self
              .arena
              .dealloc(self.allocated.memory_offset, self.allocated.memory_size);
          }
        }
      }
      Kind::Inline(_) => {
        if !self.detached {
          // SAFETY: offset and offset + size are inbounds of the ARENA.
          unsafe {
            self
              .arena
              .dealloc(self.allocated.memory_offset, self.allocated.memory_size);
          }
        }
      }
      Kind::Dangling(_) => {}
    }
  }
}
