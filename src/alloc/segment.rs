use super::*;

pub(super) struct SegmentNode<S: Size> {
  pub(super) prev: S::Atomic,
  pub(super) next: S::Atomic,
}

pub(super) struct SegmentList<S: Size> {
  /// The head segment node offset.
  head: S::Atomic,
  /// The tail segment node offset.
  tail: S::Atomic,

  /// The total length of the available segments.
  len: S::Atomic,
}
