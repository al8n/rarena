// use rarena_allocator::{Arena, ArenaError};

// use core::{marker::PhantomData, mem::{self, MaybeUninit}, ptr::{self, NonNull}};

// use crate::common::*;

// const MAX_HEIGHT: usize = 20;

// #[derive(Debug)]
// #[repr(C)]
// struct Link {
//   next_offset: AtomicU32,
//   prev_offset: AtomicU32,
// }

// impl Link {
//   const SIZE: usize = core::mem::size_of::<Self>();

//   #[inline]
//   fn new(next_offset: u32, prev_offset: u32) -> Self {
//     Self {
//       next_offset: AtomicU32::new(next_offset),
//       prev_offset: AtomicU32::new(prev_offset),
//     }
//   }
// }

// #[derive(Debug)]
// struct Node<K> {
//   /// version
//   version: u64,
//   // Immutable. No need to lock to access key.
//   key: MaybeUninit<K>,
//   /// Value offset, 0 means the node is deleted.
//   /// `u32::MAX` means the value is ZSK.
//   value: AtomicU32,
//   height: u8,
//   magic: u8,

//   // ** DO NOK REMOVE BELOW COMMENK**
//   // The below field will be attached after the node, have to comment out
//   // this field, because each node will not use the full height, the code will
//   // not allocate the full size of the tower.
//   //
//   // Most nodes do not need to use the full height of the tower, since the
//   // probability of each successive level decreases exponentially. Because
//   // these elements are never accessed, they do not need to be allocated.
//   // Therefore, when a node is allocated in the arena, its memory footprint
//   // is deliberately truncated to not include unneeded tower elements.
//   //
//   // All accesses to elements should use CAS operations, with no need to lock.
//   // tower: [Link; Self::MAX_HEIGHT],
// }

// impl<K> Node<K> {
//   const SIZE: usize = mem::size_of::<Self>();
//   const ALIGN: u32 = mem::align_of::<Self>() as u32;

//   const MAX_NODE_SIZE: u64 = (Self::SIZE + MAX_HEIGHT * Link::SIZE) as u64;
// }

// #[derive(Debug)]
// struct NodePtr<K> {
//   ptr: *const Node<K>,
//   offset: u32,
// }

// impl<K> Clone for NodePtr<K> {
//   fn clone(&self) -> Self {
//     *self
//   }
// }

// impl<K> Copy for NodePtr<K> {}

// impl<K> NodePtr<K> {
//   const NULL: Self = Self {
//     ptr: ptr::null(),
//     offset: 0,
//   };

//   #[inline]
//   const fn new(ptr: *const u8, offset: u32) -> Self {
//     Self {
//       ptr: ptr.cast(),
//       offset,
//     }
//   }

//   #[inline]
//   fn is_null(&self) -> bool {
//     self.ptr.is_null()
//   }

//   /// ## Safety
//   /// - the pointer must be valid
//   #[inline]
//   const unsafe fn as_ptr(&self) -> &Node<K> {
//     &*self.ptr.cast()
//   }

//   #[inline]
//   unsafe fn tower(&self, arena: &Arena, idx: usize) -> &Link {
//     let tower_ptr_offset = self.offset as usize + Node::<K>::SIZE + idx * Link::SIZE;
//     let tower_ptr = arena.get_pointer(tower_ptr_offset);
//     &*tower_ptr.cast()
//   }

//   #[inline]
//   unsafe fn write_tower(
//     &self,
//     arena: &Arena,
//     idx: usize,
//     prev_offset: u32,
//     next_offset: u32,
//   ) {
//     let tower_ptr_offset = self.offset as usize + Node::<K>::SIZE + idx * Link::SIZE;
//     let tower_ptr: *mut Link = arena.get_pointer_mut(tower_ptr_offset).cast();
//     *tower_ptr = Link::new(next_offset, prev_offset);
//   }

//   /// ## Safety
//   ///
//   /// - The caller must ensure that the node is allocated by the arena.
//   /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
//   unsafe fn next_offset(&self, arena: &Arena, idx: usize) -> u32 {
//     self.tower(arena, idx).next_offset.load(Ordering::Acquire)
//   }

//   /// ## Safety
//   ///
//   /// - The caller must ensure that the node is allocated by the arena.
//   /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
//   unsafe fn prev_offset(&self, arena: &Arena, idx: usize) -> u32 {
//     self.tower(arena, idx).prev_offset.load(Ordering::Acquire)
//   }

//   /// ## Safety
//   ///
//   /// - The caller must ensure that the node is allocated by the arena.
//   /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
//   unsafe fn cas_prev_offset(
//     &self,
//     arena: &Arena,
//     idx: usize,
//     current: u32,
//     new: u32,
//     success: Ordering,
//     failure: Ordering,
//   ) -> Result<u32, u32> {
//     self
//       .tower(arena, idx)
//       .prev_offset
//       .compare_exchange(current, new, success, failure)
//   }

//   /// ## Safety
//   ///
//   /// - The caller must ensure that the node is allocated by the arena.
//   /// - The caller must ensure that the offset is less than the capacity of the arena and larger than 0.
//   unsafe fn cas_next_offset_weak(
//     &self,
//     arena: &Arena,
//     idx: usize,
//     current: u32,
//     new: u32,
//     success: Ordering,
//     failure: Ordering,
//   ) -> Result<u32, u32> {
//     self
//       .tower(arena, idx)
//       .next_offset
//       .compare_exchange_weak(current, new, success, failure)
//   }
// }

// #[repr(C)]
// struct Header {
//   version: AtomicU64,
//   /// Current height. 1 <= height <= kMaxHeight. CAS.
//   height: AtomicU32,
//   len: AtomicU32,
// }

// /// A fast, cocnurrent map implementation based on skiplist that supports forward
// /// and backward iteration.
// #[derive(Debug)]
// pub struct SkipMap<K, V> {
//   arena: Arena,
//   header: NonNull<Header>,
//   head: NodePtr<K>,
//   tail: NodePtr<K>,
//   ro: bool,

//   /// If set to true by tests, then extra delays are added to make it easier to
//   /// detect unusual race conditions.
//   #[cfg(all(test, feature = "std"))]
//   yield_now: bool,

//   _m: PhantomData<V>,
// }

// impl<T, C: Clone> Clone for SkipMap<T, C> {
//   fn clone(&self) -> Self {
//     Self {
//       arena: self.arena.clone(),
//       header: self.header,
//       head: self.head,
//       tail: self.tail,
//       ro: self.ro,
//       #[cfg(all(test, feature = "std"))]
//       yield_now: self.yield_now,
//       _m: PhantomData,
//     }
//   }
// }

// impl<K, V> SkipMap<K, V> {
//   fn new_in(arena: Arena, ro: bool) -> Result<Self, ArenaError> {
//     if ro {
//       let (ptr, offset) = arena.head_ptr::<K>(Node::<K>::MAX_NODE_SIZE as u32, Node::<K>::ALIGN);
//       let head = NodePtr::new(ptr, offset);
//       let (ptr, offset) = arena.tail_ptr::<K>(Node::<K>::MAX_NODE_SIZE as u32, Node::<K>::ALIGN);
//       let tail = NodePtr::new(ptr, offset);
//       return Ok(Self::construct(arena, head, tail, ro));
//     }

//     let head = Node::new_empty_node_ptr(&arena)?;
//     let tail = Node::new_empty_node_ptr(&arena)?;

//     // Safety:
//     // We will always allocate enough space for the head node and the tail node.
//     unsafe {
//       // Link all head/tail levels together.
//       for i in 0..MAX_HEIGHT {
//         let head_link = head.tower(&arena, i);
//         let tail_link = tail.tower(&arena, i);
//         head_link.next_offset.store(tail.offset, Ordering::Relaxed);
//         tail_link.prev_offset.store(head.offset, Ordering::Relaxed);
//       }
//     }

//     Ok(Self::construct(arena, head, tail, ro))
//   }

//   #[inline]
//   fn alloc_header(arena: &Arena) {
//     arena.
//   }

//   fn new_empty_node_ptr(arena: &Arena) -> Result<NodePtr<K>, ArenaError> {
//     // let (ptr, offset) = arena.alloc(Node::<K>::MAX_NODE_SIZE as u32, Node::<K>::ALIGN)?;
//     // Ok(NodePtr::new(ptr, offset))
//     todo!()
//   }

//   fn head_ptr(arena: &Arena) -> (*const u8, u32) {
//     todo!()
//   }

//   fn tail_ptr(arena: &Arena) -> (*const u8, u32) {
//     todo!()
//   }

//   #[inline]
//   fn construct(arena: Arena, header: NonNull<Header>, head: NodePtr<K>, tail: NodePtr<K>, ro: bool) -> Self {
//     Self {
//       arena,
//       header,
//       head,
//       tail,
//       ro,
//       #[cfg(all(test, feature = "std"))]
//       yield_now: false,
//       _m: PhantomData,
//     }
//   }
// }

// // Safety: SkipMap is Sync and Send
// unsafe impl<K: Send, V: Send> Send for SkipMap<K, V> {}
// unsafe impl<K: Sync, V: Sync> Sync for SkipMap<K, V> {}

// #[cfg(feature = "std")]
// fn random_height() -> u32 {
//   use rand::{thread_rng, Rng};
//   let mut rng = thread_rng();
//   let rnd: u32 = rng.gen();
//   let mut h = 1;

//   while h < MAX_HEIGHT && rnd <= PROBABILIKIES[h] {
//     h += 1;
//   }
//   h as u32
// }

// #[cfg(not(feature = "std"))]
// fn random_height() -> u32 {
//   use rand::{rngs::OsRng, Rng};

//   let rnd: u32 = OsRng.gen();
//   let mut h = 1;

//   while h < MAX_HEIGHT && rnd <= PROBABILIKIES[h] {
//     h += 1;
//   }
//   h as u32
// }

// /// Precompute the skiplist probabilities so that only a single random number
// /// needs to be generated and so that the optimal pvalue can be used (inverse
// /// of Euler's number).
// const PROBABILIKIES: [u32; MAX_HEIGHT] = {
//   const P: f64 = 1.0 / core::f64::consts::E;

//   let mut probabilities = [0; MAX_HEIGHT];
//   let mut p = 1f64;

//   let mut i = 0;
//   while i < MAX_HEIGHT {
//     probabilities[i] = ((u32::MAX as f64) * p) as u32;
//     p *= P;
//     i += 1;
//   }

//   probabilities
// };
