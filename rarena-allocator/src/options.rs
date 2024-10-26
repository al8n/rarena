use core::mem;

use crate::align_offset;

use super::{Allocator, Error};

/// Unknown freelist error.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
#[repr(transparent)]
pub struct UnknownFreelist(());

impl core::fmt::Display for UnknownFreelist {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "unknown freelist")
  }
}

#[cfg(feature = "std")]
impl std::error::Error for UnknownFreelist {}

/// The freelist configuration for the ARENA.
#[derive(Default, Debug, Clone, Copy, Eq, PartialEq, Hash)]
#[repr(u8)]
#[non_exhaustive]
pub enum Freelist {
  /// Disable freelist, once main memory is consumed out, then this ARENA cannot allocate anymore.
  None = 0,

  /// A lock-free linked list which ordered by segment size (descending), when the main memory is consumed out, the following allocation will just use the head (largest segment) from freelist.
  #[default]
  Optimistic = 1,

  /// A lock-free linked list which ordered by segment size (ascending), when the main memory is consumed out, the following allocation will find the most suitable segment from freelist.
  Pessimistic = 2,
}

impl TryFrom<u8> for Freelist {
  type Error = UnknownFreelist;

  fn try_from(value: u8) -> Result<Self, Self::Error> {
    Ok(match value {
      0 => Self::None,
      1 => Self::Optimistic,
      2 => Self::Pessimistic,
      _ => return Err(UnknownFreelist(())),
    })
  }
}

/// Options for creating an ARENA
#[derive(Debug, Clone, Copy)]
pub struct Options {
  maximum_alignment: usize,
  pub(crate) capacity: Option<u32>,
  minimum_segment_size: u32,
  maximum_retries: u8,
  magic_version: u16,
  unify: bool,
  freelist: Freelist,
  reserved: u32,

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  lock_meta: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  create_new: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  create: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  read: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  write: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  append: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  truncate: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) offset: u64,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  stack: bool,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  huge: Option<u8>,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  populate: bool,
}

impl Default for Options {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl Options {
  /// Create an options for creating an ARENA with default values.
  #[inline]
  pub const fn new() -> Self {
    Self {
      maximum_alignment: 8,
      capacity: None,
      minimum_segment_size: 20,
      maximum_retries: 5,
      unify: false,
      magic_version: 0,
      freelist: Freelist::Optimistic,
      reserved: 0,

      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      lock_meta: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      create_new: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      create: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      read: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      write: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      append: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      truncate: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      offset: 0,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      stack: false,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      huge: None,
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      populate: false,
    }
  }

  /// Returns the data offset of the ARENA if the ARENA is in unified memory layout.
  ///
  /// See also [`Options::data_offset`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync, unsync, Options, Allocator};
  ///
  /// // Create a sync ARENA.
  /// let opts = Options::new().with_capacity(100);
  /// let data_offset_from_opts = opts.data_offset::<sync::Arena>();
  /// let arena = opts.alloc::<sync::Arena>().unwrap();
  /// assert_eq!(data_offset_from_opts, arena.data_offset());
  ///
  /// let data_offset_from_opts = opts.data_offset_unify::<sync::Arena>();
  /// let arena = opts.with_unify(true).alloc::<sync::Arena>().unwrap();
  /// assert_eq!(data_offset_from_opts, arena.data_offset());
  ///
  /// // Create a unsync ARENA.
  /// let opts = Options::new().with_capacity(100);
  /// let data_offset_from_opts = opts.data_offset::<unsync::Arena>();
  /// let arena = opts.alloc::<unsync::Arena>().unwrap();
  /// assert_eq!(data_offset_from_opts, arena.data_offset());
  ///
  /// let data_offset_from_opts = opts.data_offset_unify::<unsync::Arena>();
  /// let arena = opts.with_unify(true).alloc::<unsync::Arena>().unwrap();
  /// assert_eq!(data_offset_from_opts, arena.data_offset());
  /// ```
  pub fn data_offset_unify<A: Allocator>(&self) -> usize {
    let reserved = self.reserved() as usize;
    Self::data_offset_in::<A::Header>(reserved, true)
  }

  /// Returns the data offset of the ARENA if the ARENA is not in unified memory layout.
  ///
  /// As the file backed ARENA will only use the unified memory layout and ignore the unify configuration of `Options`,
  /// so see also [`Options::data_offset_unify`], if you want to get the data offset of the ARENA in unified memory layout.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync, unsync, Options, Allocator};
  ///
  /// // Create a sync ARENA.
  /// let opts = Options::new().with_capacity(100);
  /// let data_offset_from_opts = opts.data_offset::<sync::Arena>();
  /// let arena = opts.alloc::<sync::Arena>().unwrap();
  /// assert_eq!(data_offset_from_opts, arena.data_offset());
  ///
  /// let data_offset_from_opts = opts.data_offset_unify::<sync::Arena>();
  /// let arena = opts.with_unify(true).alloc::<sync::Arena>().unwrap();
  /// assert_eq!(data_offset_from_opts, arena.data_offset());
  ///
  /// // Create a unsync ARENA.
  /// let opts = Options::new().with_capacity(100);
  /// let data_offset_from_opts = opts.data_offset::<unsync::Arena>();
  /// let arena = opts.alloc::<unsync::Arena>().unwrap();
  /// assert_eq!(data_offset_from_opts, arena.data_offset());
  ///
  /// let data_offset_from_opts = opts.data_offset_unify::<unsync::Arena>();
  /// let arena = opts.with_unify(true).alloc::<unsync::Arena>().unwrap();
  /// assert_eq!(data_offset_from_opts, arena.data_offset());
  /// ```
  pub fn data_offset<A: Allocator>(&self) -> usize {
    let reserved = self.reserved() as usize;
    Self::data_offset_in::<A::Header>(reserved, false)
  }

  #[inline]
  fn data_offset_in<H>(reserved: usize, unify: bool) -> usize {
    if unify {
      let offset = align_offset::<H>(reserved as u32) as usize + mem::align_of::<H>();
      offset + mem::size_of::<H>()
    } else {
      reserved + 1
    }
  }

  /// Set the reserved of the ARENA.
  ///
  /// The reserved is used to configure the start position of the ARENA. This is useful
  /// when you want to add some bytes before the ARENA, e.g. when using the memory map file backed ARENA,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_reserved(8);
  /// ```
  #[inline]
  pub const fn with_reserved(mut self, reserved: u32) -> Self {
    self.reserved = reserved;
    self
  }

  /// Set the maximum alignment of the ARENA.
  ///
  /// If you are trying to allocate a `T` which requires a larger alignment than this value,
  /// then will lead to `read_unaligned`, which is undefined behavior on some platforms.
  ///
  /// The alignment must be a power of 2.
  /// The default maximum alignment is `8`.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_maximum_alignment(16);
  /// ```
  #[inline]
  pub const fn with_maximum_alignment(mut self, alignment: usize) -> Self {
    assert!(
      alignment.is_power_of_two(),
      "alignment must be a power of 2"
    );
    self.maximum_alignment = alignment;
    self
  }

  /// Set the capacity of the ARENA. If the ARENA is backed by a memory map and the original file size is less than the capacity,
  /// then the file will be resized to the capacity.
  ///
  /// For vec backed ARENA and anonymous memory map backed ARENA, this configuration is required.
  ///
  /// For file backed ARENA, this configuration is optional, if the capacity is not set, then the capacity will be the original file size.
  ///
  /// The capacity must be greater than the minimum capacity of the ARENA.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_capacity(2048);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = Some(capacity);
    self
  }

  /// Set or unset the capacity of the ARENA. If the ARENA is backed by a memory map and the original file size is less than the capacity,
  /// then the file will be resized to the capacity.
  ///
  /// For vec backed ARENA and anonymous memory map backed ARENA, this configuration is required.
  ///
  /// For file backed ARENA, this configuration is optional, if the capacity is not set, then the capacity will be the original file size.
  ///
  /// The capacity must be greater than the minimum capacity of the ARENA.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_capacity(2048);
  ///
  /// /// some business logic
  /// let opts = opts.maybe_capacity(None);
  /// ```
  #[inline]
  pub const fn maybe_capacity(mut self, capacity: Option<u32>) -> Self {
    self.capacity = capacity;
    self
  }

  /// Set the minimum segment size of the ARENA.
  ///
  /// This value controls the size of the holes.
  ///
  /// The default minimum segment size is `48 bytes`.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_minimum_segment_size(64);
  /// ```
  #[inline]
  pub const fn with_minimum_segment_size(mut self, minimum_segment_size: u32) -> Self {
    self.minimum_segment_size = minimum_segment_size;
    self
  }

  /// Set the maximum retries of the ARENA.
  ///
  /// This value controls how many times the ARENA will retry to allocate from slow path.
  ///
  /// The default maximum retries is `5`.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_maximum_retries(10);
  /// ```
  #[inline]
  pub const fn with_maximum_retries(mut self, maximum_retries: u8) -> Self {
    self.maximum_retries = maximum_retries;
    self
  }

  /// Set if use the unify memory layout of the ARENA.
  ///
  /// File backed ARENA has different memory layout with other kind backed ARENA,
  /// set this value to `true` will unify the memory layout of the ARENA, which means
  /// all kinds of backed ARENA will have the same memory layout.
  ///
  /// This value will be ignored if the ARENA is backed by a file backed memory map.
  ///
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_unify(true);
  /// ```
  #[inline]
  pub const fn with_unify(mut self, unify: bool) -> Self {
    self.unify = unify;
    self
  }

  /// Set the external version of the ARENA,
  /// this is used by the application using [`Allocator`](crate::Allocator)
  /// to ensure that it doesn't open the [`Allocator`](crate::Allocator)
  /// with incompatible data format.
  ///
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.magic_version = magic_version;
    self
  }

  /// Set the freelist configuration for the ARENA.
  /// The default freelist is `Freelist::Optimistic`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{Options, Freelist};
  ///
  /// let opts = Options::new().with_freelist(Freelist::Pessimistic);
  /// ```
  #[inline]
  pub const fn with_freelist(mut self, freelist: Freelist) -> Self {
    self.freelist = freelist;
    self
  }

  /// Get the reserved of the ARENA.
  ///
  /// The reserved is used to configure the start position of the ARENA. This is useful
  /// when you want to add some bytes before the ARENA, e.g. when using the memory map file backed ARENA,
  /// you can set the reserved to the size to `8` to store a 8 bytes checksum.
  ///
  /// The default reserved is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_reserved(8);
  ///
  /// assert_eq!(opts.reserved(), 8);
  /// ```
  #[inline]
  pub const fn reserved(&self) -> u32 {
    self.reserved
  }

  /// Get the maximum alignment of the ARENA.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_maximum_alignment(16);
  ///
  /// assert_eq!(opts.maximum_alignment(), 16);
  /// ```
  #[inline]
  pub const fn maximum_alignment(&self) -> usize {
    self.maximum_alignment
  }

  /// Get the capacity of the ARENA.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_capacity(2048);
  ///
  /// assert_eq!(opts.capacity(), 2048);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    match self.capacity {
      Some(capacity) => capacity,
      None => 0,
    }
  }

  /// Get the minimum segment size of the ARENA.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_minimum_segment_size(64);
  ///
  /// assert_eq!(opts.minimum_segment_size(), 64);
  /// ```
  #[inline]
  pub const fn minimum_segment_size(&self) -> u32 {
    self.minimum_segment_size
  }

  /// Get the maximum retries of the ARENA.
  /// This value controls how many times the ARENA will retry to allocate from slow path.
  ///
  /// The default maximum retries is `5`.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_maximum_retries(10);
  ///
  /// assert_eq!(opts.maximum_retries(), 10);
  /// ```
  #[inline]
  pub const fn maximum_retries(&self) -> u8 {
    self.maximum_retries
  }

  /// Get if use the unify memory layout of the ARENA.
  ///
  /// File backed ARENA has different memory layout with other kind backed ARENA,
  /// set this value to `true` will unify the memory layout of the ARENA, which means
  /// all kinds of backed ARENA will have the same memory layout.
  ///
  /// This value will be ignored if the ARENA is backed by a file backed memory map.
  ///  
  /// The default value is `false`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_unify(true);
  ///
  /// assert_eq!(opts.unify(), true);
  /// ```
  #[inline]
  pub const fn unify(&self) -> bool {
    self.unify
  }

  /// Get the external version of the ARENA,
  /// this is used by the application using [`Allocator`](crate::Allocator)
  /// to ensure that it doesn't open the [`Allocator`](crate::Allocator)
  /// with incompatible data format.
  ///
  /// The default value is `0`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::Options;
  ///
  /// let opts = Options::new().with_magic_version(1);
  ///
  /// assert_eq!(opts.magic_version(), 1);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.magic_version
  }

  /// Get the freelist configuration for the ARENA.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{Options, Freelist};
  ///
  /// let opts = Options::new().with_freelist(Freelist::Pessimistic);
  ///
  /// assert_eq!(opts.freelist(), Freelist::Pessimistic);
  /// ```
  #[inline]
  pub const fn freelist(&self) -> Freelist {
    self.freelist
  }
}

macro_rules! constructor {
  ($this:ident.$fn:ident ($($path:ident)?)) => {{
    $crate::memory::Memory::<A::RefCounter, A::PathRefCounter, A::Header>::$fn($($path,)? $this).map(::core::convert::Into::into)
  }};
}

impl Options {
  /// Create a new [`Allocator`](super::Allocator) which is backed by a `Vec`.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync, unsync, Options};
  ///
  /// // Create a sync ARENA.
  /// let arena = Options::new().with_capacity(100).alloc::<sync::Arena>().unwrap();
  ///
  /// // Create a unsync ARENA.
  /// let arena = Options::new().with_capacity(100).alloc::<unsync::Arena>().unwrap();
  /// ```
  #[inline]
  pub fn alloc<A: Allocator>(self) -> Result<A, Error> {
    constructor!(self.alloc())
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
mod open_options;
