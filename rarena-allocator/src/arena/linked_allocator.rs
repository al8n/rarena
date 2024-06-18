use core::{mem, ptr::NonNull};

use super::*;

const SENTINEL_NODE_SIZE: u32 = u32::MAX;
const SENTINEL_NODE_OFFSET: u32 = u32::MAX;
const REMOVED_NODE: u32 = 0;
const SLOT_ID_SIZE: u32 = mem::size_of::<u32>() as u32;
const NODE_SIZE: u32 = mem::size_of::<Node>() as u32 + SLOT_ID_SIZE;

#[repr(C, align(8))]
struct Node {
  size_and_next_offset: AtomicU64,
  // *DO NOT REMOVE THE COMMENT OUT CODE*
  // Each node will follow by a slot number, comment out so that the node alignment is the same as AtomicU64.
  // slot: u32,
}

impl core::ops::Deref for Node {
  type Target = AtomicU64;

  fn deref(&self) -> &Self::Target {
    &self.size_and_next_offset
  }
}

struct Header {
  /// The first 32 bits store the size of the list.
  /// The last 32 bits store the pointer to the next node.
  sentinel: Node,
  /// The length of the linked list.
  len: AtomicU32,
  /// The increment version number, use to make sure the insertion is linearizable.
  /// This version number may not be consecutive.
  slot: AtomicU32,
}

/// The slot id for the segment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SlotId(u32);

/// The mutable slot.
pub struct SlotMut<'a> {
  slot: SlotId,
  buf: &'a mut [u8],
}

impl SlotMut<'_> {
  /// Returns the slot id.
  #[inline]
  pub const fn id(&self) -> SlotId {
    self.slot
  }
}

impl core::ops::Deref for SlotMut<'_> {
  type Target = [u8];

  fn deref(&self) -> &Self::Target {
    self.buf
  }
}

impl core::ops::DerefMut for SlotMut<'_> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    self.buf
  }
}

impl core::fmt::Debug for SlotMut<'_> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("SlotMut")
      .field("id", &self.slot)
      .field("buf", &self.buf)
      .finish()
  }
}

/// The immutable slot.
pub struct SlotRef<'a> {
  slot: SlotId,
  buf: &'a [u8],
}

impl SlotRef<'_> {
  /// Returns the slot id.
  #[inline]
  pub const fn id(&self) -> SlotId {
    self.slot
  }
}

impl core::ops::Deref for SlotRef<'_> {
  type Target = [u8];

  fn deref(&self) -> &Self::Target {
    self.buf
  }
}

impl core::fmt::Debug for SlotRef<'_> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_struct("SlotRef")
      .field("id", &self.slot)
      .field("buf", &self.buf)
      .finish()
  }
}

/// Singly linked allocator.
/// 
/// The linked allocator is a lock-free singly linked list allocator.
/// Compared to directly using the [`Arena`], the linked allocator supports
/// iterating over the allocated segments, which helps in some functionalities,
/// e.g. replay or rewrite logic when implementing lock-free append-only log.
pub struct LinkedAllocator {
  arena: Arena,
  header: NonNull<Header>,
}

unsafe impl Send for LinkedAllocator {}
unsafe impl Sync for LinkedAllocator {}

impl LinkedAllocator {
  // /// Allocates bytes from the linked allocator.
  // pub fn alloc_bytes(&self, val_size: u32) -> Result<BytesRefMut, Error> {
  //   let mut segment = self.arena.alloc_aligned_bytes::<AtomicU64>(val_size)?;
  //   segment.detach();
  //   let backoff = Backoff::new();
  //   let header = self.header();
  //   loop {
  //     let sentinel = &header.sentinel;
  //     let sentinel_node = sentinel.load(Ordering::Acquire);
  //     let (size, head_offset) = decode_node(sentinel_node);
  //     // The list is empty, directly insert the new node.
  //     if head_offset == SENTINEL_NODE_OFFSET {
  //       let new_sentinel = encode_node(SENTINEL_NODE_SIZE, segment.offset() as u32);

  //       // CAS the sentinel node.
  //       if sentinel.compare_exchange(sentinel_node, new_sentinel, Ordering::AcqRel, Ordering::Relaxed).is_err() {
  //         backoff.spin();
  //         continue;
  //       }
  //     }

  //     // SAFETY: when inserting a new node, we make sure the offset is the well-aligned.
  //     let head = unsafe { &*self.arena.get_pointer(head_offset as usize).cast::<AtomicU64>() };
  //     let head_node = head.load(Ordering::Acquire);
  //     let (head_size, _) = decode_node(head_node);

  //     if head_size == REMOVED_NODE {
  //       // The head node is removed, retry.
  //       // let other threads to make progress.
  //       backoff.snooze();
  //       continue;
  //     }
      
  //     unsafe {
  //       // SAFETY: alloc_aligned_bytes ensures the segment is well-aligned.
  //       segment.put_unchecked(AtomicU64::new(encode_node(val_size, head_offset)));
  //     };

  //     let new_sentinel = encode_node(size, segment.offset() as u32);

  //     // CAS the sentinel node.
  //     match sentinel.compare_exchange(sentinel_node, new_sentinel, Ordering::AcqRel, Ordering::Relaxed) {
  //       Ok(_) => {
  //         header.len.fetch_add(1, Ordering::Release);
  //         let mut meta = segment.allocated;
  //         let padding = meta.ptr_offset - meta.memory_offset;
  //         meta.memory_size = meta.memory_size - mem::size_of::<AtomicU64>() as u32 - padding;
  //         meta.memory_offset = meta.ptr_offset + mem::size_of::<AtomicU64>() as u32;
  //         meta.ptr_offset = meta.memory_offset;
  //         meta.ptr_size = meta.memory_size;
  //         // SAFETY: alloc_aligned_bytes ensures the segment has enough space.
  //         return Ok(unsafe { BytesRefMut::new(&self.arena, meta) });
  //       },
  //       Err(_) => backoff.spin(),
  //     }
  //   }
  // }

  // /// See [`Arena::alloc`].
  // pub fn alloc<T>(&self) -> Result<RefMut<T>, Error> {
  //   let padding = padding::<T>();
  //   let want = padding + mem::size_of::<T>();
  //   let mut bytes = self.alloc_bytes(want as u32)?;
  //   bytes.detach();

  //   let ptr = bytes.as_mut_ptr();
  //   unsafe {
  //     let ptr = ptr.add(padding);
  //     let mut meta = bytes.allocated;
  //     meta.ptr_offset = meta.memory_offset + padding as u32;
  //     meta.ptr_size = mem::size_of::<T>() as u32;
  //     if mem::needs_drop::<T>() {
  //       let ptr: *mut MaybeUninit<T> = ptr.cast();
  //       ptr::write(ptr, MaybeUninit::uninit());
  //       Ok(RefMut::new(ptr::read(ptr), meta, &self.arena))
  //     } else {
  //       Ok(RefMut::new_inline(NonNull::new_unchecked(ptr.cast()), meta, &self.arena))
  //     }
  //   }
  // }

  /// j
  pub fn alloc(&self, size: u32) -> Result<SlotMut, Error> {
    if self.arena.ro {
      return Err(Error::ReadOnly);
    }

    // fetch the slot id for the new segment.
    let slot = self.header().slot.fetch_add(1, Ordering::AcqRel);
    let mut node = self.arena.alloc_aligned_bytes::<AtomicU64>(size + SLOT_ID_SIZE)?;
    let node_ptr = node.as_mut_ptr();
    let offset = node.offset() as u32 + NODE_SIZE;
    node.detach();

    // once node is allocated, then the space will never be reclaimed.
    // so we need to increase the discarded space.
    self.arena.increase_discarded(NODE_SIZE);

    unsafe {
      // SAFETY: alloc_aligned_bytes ensures the segment is well-aligned.
      node.put_unchecked::<AtomicU64>(AtomicU64::new(encode_node(
        size,
        // give the next to sentinel, this value will be updated later.
        SENTINEL_NODE_OFFSET,
      )));
      // SAFETY: alloc_aligned_bytes ensures the segment has enough space.
      node.put_u32_le_unchecked(slot);
    }

    let backoff = Backoff::new();
    let header = self.header();

    loop {
      let (prev_node_size_and_next_node_offset, prev) = self
        .find_position(slot);
      let (prev_node_size, next_node_offset) =
        decode_segment_node(prev_node_size_and_next_node_offset);

      if prev_node_size == REMOVED_NODE {
        // wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // update the node
      unsafe {
        (*node_ptr.cast::<Node>()) = Node {
          size_and_next_offset: AtomicU64::new(encode_node(size, next_node_offset)),
        };
      }

      match prev.compare_exchange(
        prev_node_size_and_next_node_offset,
        encode_segment_node(prev_node_size, offset),
        Ordering::AcqRel,
        Ordering::Relaxed,
      ) {
        Ok(_) => {
          header.len.fetch_add(1, Ordering::Release);
          // SAFETY: alloc_aligned_bytes ensures the segment has enough space.
          return Ok(SlotMut {
            slot: SlotId(slot),
            buf: unsafe { slice::from_raw_parts_mut(node_ptr.add((offset + NODE_SIZE) as usize), size as usize) },
          });
        }
        Err(current) => {
          let (size, _) = decode_segment_node(current);
          // the current is removed from the list, then we need to refind the position.
          if size == REMOVED_NODE {
            // wait other thread to make progress.
            backoff.snooze();
          } else {
            backoff.spin();
          }
        }
      }
    }
  }

  /// Deallocates the slot.
  pub fn dealloc(&self, slot: SlotId) {
    let slot = slot.0;

    let header = self.header();
    let mut current: &AtomicU64 = &header.sentinel;
    let mut current_node = current.load(Ordering::Acquire);
    let (mut current_node_size, mut next_offset) = decode_segment_node(current_node);
    let backoff = Backoff::new();
    loop {
      // the list is empty
      if current_node_size == SENTINEL_NODE_SIZE
        && next_offset == SENTINEL_NODE_OFFSET
      {
        return;
      }

      // the current is marked as remove and the next is the tail.
      if current_node_size == REMOVED_NODE && next_offset == SENTINEL_NODE_OFFSET {
        return;
      }

      if current_node_size == REMOVED_NODE {
        current = if next_offset == SENTINEL_NODE_OFFSET {
          return;
        } else {
          unsafe { self.get_node(next_offset) }
        };
        current_node = current.load(Ordering::Acquire);
        (current_node_size, next_offset) = decode_segment_node(current_node);
        continue;
      }

      // the next is the tail, then we should insert the value after the current node.
      if next_offset == SENTINEL_NODE_OFFSET {
        return;
      }

      let next = unsafe { self.get_node(next_offset) };
      let next_node = next.load(Ordering::Acquire);
      let (next_node_size, next_next_offset) = decode_segment_node(next_node);

      let next_node_slot = unsafe { self.get_slot(next_offset + SLOT_ID_SIZE) };
      // the slot is already removed.
      if slot > next_node_slot {
        return;
      }

      // found the slot, then mark the node as removed.
      if slot == next_node_slot {
        let removed_node = encode_segment_node(REMOVED_NODE, next_next_offset);

        // try mark the next node as removed.
        if let Err(updated_next_node) = next.compare_exchange(next_node, removed_node, Ordering::AcqRel, Ordering::Relaxed) {
          let (updated_next_node_size, _) = decode_segment_node(updated_next_node);

          if updated_next_node_size != REMOVED_NODE {
            // the next node is up
            backoff.snooze();
            continue;
          }
        }

        // we have marked the next node as removed, then we can try to update the current node.
        let new_next_node = encode_segment_node(current_node_size, next_next_offset);
        match current.compare_exchange(current_node, new_next_node, Ordering::AcqRel, Ordering::Relaxed) {
          Ok(_) => {
            // deallocate the node.
            unsafe { self.arena.dealloc(next_offset + NODE_SIZE, next_node_size) };
            header.len.fetch_sub(1, Ordering::Release);
            return;
          }
          Err(_) => {
            backoff.spin();
          }
        }
        return;
      }

      current = next;
      current_node = next_node;
      current_node_size = next_node_size;
      next_offset = next_next_offset;
    }
  }

  /// Returns the free list position to insert the value.
  /// - `None` means that we should insert to the head.
  /// - `Some(offset)` means that we should insert after the offset. offset -> new -> next
  fn find_position(&self, slot: u32) -> (u64, &AtomicU64) {
    let header = self.header();
    let mut current: &AtomicU64 = &header.sentinel;
    let mut current_node = current.load(Ordering::Acquire);
    let (mut current_node_size, mut next_offset) = decode_segment_node(current_node);
    let backoff = Backoff::new();
    loop {
      // the list is empty
      if current_node_size == SENTINEL_NODE_SIZE
        && next_offset == SENTINEL_NODE_OFFSET
      {
        return (current_node, current);
      }

      // the current is marked as remove and the next is the tail.
      if current_node_size == REMOVED_NODE && next_offset == SENTINEL_NODE_OFFSET {
        return (current_node, current);
      }

      if current_node_size == REMOVED_NODE {
        current = if next_offset == SENTINEL_NODE_OFFSET {
          backoff.snooze();
          &header.sentinel
        } else {
          unsafe { self.get_node(next_offset) }
        };
        current_node = current.load(Ordering::Acquire);
        (current_node_size, next_offset) = decode_segment_node(current_node);
        continue;
      }

      // the next is the tail, then we should insert the value after the current node.
      if next_offset == SENTINEL_NODE_OFFSET {
        return (current_node, current);
      }

      let next = unsafe { self.get_node(next_offset) };
      let next_node = next.load(Ordering::Acquire);
      let (next_node_size, next_next_offset) = decode_segment_node(next_node);
      if next_node_size == REMOVED_NODE {
        backoff.snooze();
        continue;
      }

      let next_node_slot = unsafe { self.get_slot(next_offset + SLOT_ID_SIZE) };
      if slot >= next_node_slot {
        return (current_node, current);
      }

      current = next;
      current_node = next_node;
      current_node_size = next_node_size;
      next_offset = next_next_offset;
    }
  }

  #[allow(clippy::type_complexity)]
  fn find_prev_and_next(
    &self,
    slot: u32,
  ) -> Option<((u64, &AtomicU64), (u64, &AtomicU64))> {
    let header = self.header();
    let mut current: &AtomicU64 = &header.sentinel;
    let mut current_node = current.load(Ordering::Acquire);
    let (mut current_node_size, mut next_offset) = decode_segment_node(current_node);
    let backoff = Backoff::new();
    loop {
      // the list is empty
      if current_node_size == SENTINEL_NODE_SIZE
        && next_offset == SENTINEL_NODE_OFFSET
      {
        return None;
      }

      // the current is marked as remove and the next is the tail.
      if current_node_size == REMOVED_NODE && next_offset == SENTINEL_NODE_OFFSET {
        return None;
      }

      if current_node_size == REMOVED_NODE {
        current = if next_offset == SENTINEL_NODE_OFFSET {
          return None;
        } else {
          unsafe { self.get_node(next_offset) }
        };
        current_node = current.load(Ordering::Acquire);
        (current_node_size, next_offset) = decode_segment_node(current_node);
        continue;
      }

      // the next is the tail
      if next_offset == SENTINEL_NODE_OFFSET {
        return None;
      }

      let next = unsafe { self.get_node(next_offset) };
      let next_node = next.load(Ordering::Acquire);
      let (next_node_size, next_next_offset) = decode_segment_node(next_node);
      let next_slot = unsafe { self.get_slot(next_offset + mem::size_of::<AtomicU64>() as u32) };

      if slot <= next_slot {
        if next_node_size == REMOVED_NODE {
          backoff.snooze();
          continue;
        }

        return Some(((current_node, current), (next_node, next)));
      }

      current = unsafe { self.get_node(next_offset) };
      current_node = next_node;
      current_node_size = next_node_size;
      next_offset = next_next_offset;
    }
  }

  /// # Safety
  /// - offset must be a well-aligned pointer for u32.
  const unsafe fn get_slot(&self, offset: u32) -> u32 {
    self.arena.get_pointer(offset as usize).cast::<u32>().read()
  }

  /// # Safety
  /// - offset must be a well-aligned pointer for AtomicU64.
  const unsafe fn get_node(&self, offset: u32) -> &AtomicU64 {
    &*self.arena.get_pointer(offset as usize).cast::<AtomicU64>()
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

#[inline]
const fn padding<T>() -> usize {
  let align = mem::align_of::<T>();
  // the code will make sure offset is always a multiple of 8, so we can safely use 8 here.
  (align - 8 % align) % align
}
