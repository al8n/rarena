use super::*;

use crate::{common::*, utils::{compose_tag, decompose_tag}};

#[repr(C)]
pub(super) struct SegmentNode {
  pub(super) next: AtomicU32,
  pub(super) prev: AtomicU32,
  pub(super) len: u32,
  pub(super) ptr: u32,
}

impl SegmentNode {
  pub(super) const SIZE: usize = mem::size_of::<Self>();
  pub(super) const ALIGN: usize = mem::align_of::<Self>();

  pub(super) fn with_tag(ptr: *mut Self, tag: usize) -> *mut Self {
    compose_tag::<Self>(ptr as _, tag) as _
  }

  fn tag(&self) -> usize {
    decompose_tag::<Self>(self as *const _ as _).1
  }
}

pub(super) struct SegmentList {
  /// Multiple parts of the value are encoded as a single `u64` so that it
  /// can be atomically loaded and stored:
  /// - next node offset: `u32` (bits 0-31)
  /// - max segment size: `u32` (bits 32-63)
  next_offset_and_max_segment: AtomicU64,
}

impl SegmentList {
  pub(super) fn new() -> Self {
    Self {
      next_offset_and_max_segment: AtomicU64::new(0),
    }
  }

  pub(super) fn push(&self, node: SegmentNode) {
    // loop {
    //   let current_value = self.next_offset_and_max_segment.load(Ordering::Acquire);
    //   let (current_offset, _) = decode(current_value);

    //   // If the list is empty, insert the node at the beginning
    //   if current_offset == 0 {
    //     node.next.store(0, Ordering::Relaxed); // No next node
    //     node.prev.store(0, Ordering::Relaxed); // No previous node
    //     let new_value = encode(node.ptr_offset, node.len);
    //     if self
    //       .next_offset_and_max_segment
    //       .compare_exchange_weak(
    //         current_value,
    //         new_value,
    //         Ordering::AcqRel,
    //         Ordering::Relaxed,
    //       )
    //       .is_ok()
    //     {
    //       // CAS succeeded, node inserted
    //       break;
    //     } else {
    //       // CAS failed, retry
    //       continue;
    //     }
    //   }

    //   // Traverse the list to find the correct position to insert the node
    //   let mut prev_offset = 0;
    //   let mut current_offset = current_offset;
    //   loop {
    //     if current_offset == 0 {
    //       // Reached the end of the list, insert the node at the end
    //       let new_value = encode(node.ptr_offset, node.len);
    //       if self
    //         .next_offset_and_max_segment
    //         .compare_exchange_weak(
    //           current_value,
    //           new_value,
    //           Ordering::AcqRel,
    //           Ordering::Relaxed,
    //         )
    //         .is_ok()
    //       {
    //         // CAS succeeded, node inserted
    //         break;
    //       } else {
    //         // CAS failed, retry
    //         continue;
    //       }
    //     }

    //     // Load the current node's length and compare with the new node's length
    //     let current_node = unsafe { self.get_node(current_offset) };
    //     if let Some(current_node) = current_node {
    //       if node.len <= current_node.len {
    //         // Found the correct position to insert the node
    //         node.prev.store(prev_offset, Ordering::Relaxed);
    //         node.next.store(current_offset, Ordering::Relaxed);
    //         // Update previous node's next pointer
    //         let prev_node = unsafe { self.get_node(prev_offset).unwrap() };
    //         prev_node.next.store(node.ptr_offset, Ordering::Release);
    //         // Update current node's previous pointer
    //         current_node.prev.store(node.ptr_offset, Ordering::Release);
    //         break;
    //       }
    //       // Move to the next node
    //       prev_offset = current_offset;
    //       current_offset = current_node.next.load(Ordering::Acquire);
    //     }
    //   }
    // }
  }
}

#[inline]
const fn encode(offset: u32, size: u32) -> u64 {
  (size as u64) << 32 | offset as u64
}

#[inline]
const fn decode(offset_and_max_segment: u64) -> (u32, u32) {
  let offset = offset_and_max_segment as u32;
  let val_size = (offset_and_max_segment >> 32) as u32;
  (offset, val_size)
}
