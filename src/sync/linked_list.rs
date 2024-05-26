use core::{
  marker::PhantomData,
  mem::{ManuallyDrop, MaybeUninit},
  ptr::NonNull,
};

use super::{
  alloc::{Arena, Size},
  sealed::Atomic,
};

#[derive(Debug)]
#[repr(C)]
pub(super) struct Link<S: Size = u32> {
  pub(super) next_offset: S::Atomic,
  pub(super) prev_offset: S::Atomic,
}

impl<S: Size> Link<S> {
  pub(super) const SIZE: usize = core::mem::size_of::<Self>();

  #[inline]
  pub(super) fn new(next_offset: S, prev_offset: S) -> Self {
    Self {
      next_offset: <S::Atomic as Atomic<S>>::new(next_offset),
      prev_offset: <S::Atomic as Atomic<S>>::new(prev_offset),
    }
  }
}

#[repr(C)]
struct Node<T, S: Size = u32> {
  link: Link<S>,
  // the offset to the arena pointer
  offset: S,
  val: MaybeUninit<T>,
}

/// Lock-free, ARENA based linked list.
pub struct LinkedList<T, S: Size = u32> {
  arena: Arena<S>,
  head: Node<T, S>,
  tail: Node<T, S>,
}

impl<T, S: Size> LinkedList<T, S> {
  /// Creates a new, empty linked list.
  pub fn new(cap: usize) -> Self {
    // Creating a new empty linked list
    let arena = Arena::<S>::new(S::ZERO);
    let head_link = Link::new(S::ZERO, S::ZERO);
    let head_node = Node {
      link: head_link,
      offset: S::ZERO,
      val: MaybeUninit::uninit(),
    };
    let tail_link = Link::new(S::ZERO, S::ZERO);
    let tail_node = Node {
      link: tail_link,
      offset: S::ZERO,
      val: MaybeUninit::uninit(),
    };

    Self {
      arena,
      head: head_node,
      tail: tail_node,
    }
  }

  /// a
  pub fn push_front(&self) {
    // +----------------+     +------------+     +----------------+
    // |      prev      |     |    node    |     |      next      |
    // | prevNextOffset |---->|            |     |                |
    // |                |<----| prevOffset |     |                |
    // |                |     | nextOffset |---->|                |
    // |                |     |            |<----| nextPrevOffset |
    // +----------------+     +------------+     +----------------+
    //
    // 1. Initialize prevOffset and nextOffset to point to prev and next.
    // 2. CAS prevNextOffset to repoint from next to nd.
    // 3. CAS nextPrevOffset to repoint from prev to nd.
  }
}

// [offset & len, prev, next, 0, 0, 0, 0, 0 ...] chunk1
//
