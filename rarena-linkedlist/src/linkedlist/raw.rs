use core::{mem, ptr::NonNull};

use crossbeam_utils::Backoff;
use rarena_allocator::{Arena, BytesRefMut, Error};

use crate::common::*;

const SENTINEL_NODE_SIZE: u32 = u32::MAX;
const SENTINEL_NODE_OFFSET: u32 = u32::MAX;
const REMOVED_NODE: u32 = 0;

struct Header {
  /// The first 32 bits store the size of the list.
  /// The last 32 bits store the pointer to the next node.
  sentinel: AtomicU64,
  /// The length of the linked list.
  len: AtomicU32,
  /// The magic version number.
  magic_version: u16,
  /// Reserved for future use.
  reserved: u16,
}

/// Singly linked allocator.
pub struct LinkedAllocator {
  arena: Arena,
  header: NonNull<Header>,
}

unsafe impl Send for LinkedAllocator {}
unsafe impl Sync for LinkedAllocator {}

impl LinkedAllocator {
  /// Puts a new node into the list.
  pub fn put_bytes(&self, val: &[u8]) -> Result<(), Error> {
    let val_size = val.len() as u32;
    let mut segment = self.arena.alloc_aligned_bytes::<AtomicU64>(val_size)?;
    segment.detach();
    let backoff = Backoff::new();
    let header = self.header();
    loop {
      let sentinel = &header.sentinel;
      let sentinel_node = sentinel.load(Ordering::Acquire);
      let (size, head_offset) = decode_node(sentinel_node);
      // The list is empty, directly insert the new node.
      if head_offset == SENTINEL_NODE_OFFSET {
        let new_sentinel = encode_node(SENTINEL_NODE_SIZE, segment.offset() as u32);

        // CAS the sentinel node.
        if sentinel.compare_exchange(sentinel_node, new_sentinel, Ordering::AcqRel, Ordering::Relaxed).is_err() {
          backoff.spin();
          continue;
        }
      }

      // SAFETY: when inserting a new node, we make sure the offset is the well-aligned.
      let head = unsafe { &*self.arena.get_pointer(head_offset as usize).cast::<AtomicU64>() };
      let head_node = head.load(Ordering::Acquire);
      let (head_size, _) = decode_node(head_node);

      if head_size == REMOVED_NODE {
        // The head node is removed, retry.
        // let other threads to make progress.
        backoff.snooze();
        continue;
      }
      
      unsafe {
        // SAFETY: alloc_aligned_bytes ensures the segment is well-aligned.
        segment.put_unchecked(AtomicU64::new(encode_node(val_size, head_offset)));
        // SAFETY: alloc_aligned_bytes ensures the segment has enough space.
        segment.put_slice_unchecked(val);
      };

      let new_sentinel = encode_node(size, segment.offset() as u32);

      // CAS the sentinel node.
      match sentinel.compare_exchange(sentinel_node, new_sentinel, Ordering::AcqRel, Ordering::Relaxed) {
        Ok(_) => {
          header.len.fetch_add(1, Ordering::Release);
          return Ok(());
        },
        Err(_) => backoff.spin(),
      }
    }
  }

  /// Pops head from the list.
  pub fn pop(&self) {
    let backoff = Backoff::new();
    let header = self.header();
    loop {
      let sentinel = &header.sentinel;
      let sentinel_node = sentinel.load(Ordering::Acquire);
      let (size, head_offset) = decode_node(sentinel_node);

      if head_offset == SENTINEL_NODE_OFFSET {
        // The list is empty.
        return;
      }

      let head = unsafe { &*self.arena.get_pointer(head_offset as usize).cast::<AtomicU64>() };
      let head_node = head.load(Ordering::Acquire);
      let (head_size, next_offset) = decode_node(head_node);

      if head_size == REMOVED_NODE {
        // The head node is removed by other threads
        // let other threads to make progress.
        backoff.snooze();
        continue;
      }

      // mark the head node as removed.
      let removed_head = encode_node(size, next_offset);
      if head.compare_exchange(head_node, removed_head, Ordering::AcqRel, Ordering::Relaxed).is_err() {
        // Other threads have operated on the head node.
        // let other threads to make progress.
        backoff.snooze();
        continue;
      }

      let new_sentinel = encode_node(size, next_offset);

      // CAS the sentinel node.
      match sentinel.compare_exchange(sentinel_node, new_sentinel, Ordering::AcqRel, Ordering::Relaxed) {
        Ok(_) => {
          // deallocate the head node.
          unsafe { self.arena.dealloc(head_offset + mem::size_of::<AtomicU64>() as u32, head_size); }
          header.len.fetch_sub(1, Ordering::Release);
          return;
        },
        Err(_) => backoff.spin(),
      }
    }
  }

  #[inline]
  const fn header(&self) -> &Header {
    unsafe { self.header.as_ref() }
  }
}

#[inline]
const fn decode_node(val: u64) -> (u32, u32) {
  ((val >> 32) as u32, val as u32)
}

#[inline]
const fn encode_node(size: u32, next: u32) -> u64 {
  ((size as u64) << 32) | next as u64
}