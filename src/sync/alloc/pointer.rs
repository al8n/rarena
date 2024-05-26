use core::{marker::PhantomData, ptr::NonNull};

use segment::SegmentNode;

use crate::utils::compose_tag;

use super::*;

pub(super) struct SharedPointer<'a, S: Size> {
  arena: &'a Arena<S>,

  /// A pointer.
  ptr: NonNull<()>,

  /// The length of the pointer
  ptr_len: usize,

  /// The offset to the parent ARENA pointer
  /// 
  /// NOTE: `arena.ptr + offset != ptr`, because for well-aligned, some padding bytes may be added.
  offset: usize,

  /// The total size of this piece of memory.
  /// 
  /// ```text
  ///                                | ------------------ len ------------------|
  /// arena ptr | ..... memory ..... | offset | .. some padding .. | ptr | .... |
  /// ```
  len: usize,
}

impl<'a, S: Size> SharedPointer<'a, S> {
  pub(super) fn read_bytes(&self) -> &[u8] {
    // SAFETY: the pointer is from the ARENA, and the length is valid.
    unsafe { slice::from_raw_parts(self.ptr.as_ptr() as *const u8, self.ptr_len) }
  }

  /// SAFETY: The caller must ensure that the pointer is well-aligned for the `T`.
  pub(super) unsafe fn read<T>(&self) -> &T {
    // SAFETY: the pointer is from the ARENA, and the length is valid.
    &*(self.ptr.as_ptr() as *const T)
  }

  pub(super) fn reclaim(self) {
    unsafe {
      // clear the memory
      let start_ptr = self.arena.ptr.add(self.offset);
      ptr::write_bytes(start_ptr, 0, self.len);

      let padded = SegmentNode::SIZE + SegmentNode::ALIGN - 1;
      // this piece of memory is too small to be a segment node
      // so we just leave it as a hole
      if padded > self.len {
        return;
      }

      // the offset to the well aligned SegmentNode
      let new_offset = self.offset & !(SegmentNode::ALIGN - 1);
      let new_len = self.len - (new_offset - self.offset);
      let node_ptr = self.arena.ptr.add(new_offset) as *mut SegmentNode;
      ptr::addr_of_mut!((*node_ptr).next).write(AtomicU32::new(0));
      ptr::addr_of_mut!((*node_ptr).prev).write(AtomicU32::new(0));
      ptr::addr_of_mut!((*node_ptr).len).write(new_len as u32);
      ptr::addr_of_mut!((*node_ptr).ptr).write(new_offset as u32);

      SegmentNode::with_tag(node_ptr as _, 0);

      // SegmentNode {
      //   next: todo!(),
      //   prev: todo!(),
      //   len: todo!(),
      //   ptr_offset: todo!(),
      // }
    }
  }
}