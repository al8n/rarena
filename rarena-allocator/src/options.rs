#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
mod open_options;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
pub use open_options::*;

/// Options for creating an ARENA
#[derive(Debug, Clone, Copy)]
pub struct ArenaOptions {
  maximum_alignment: usize,
  capacity: u32,
  minimum_segment_size: u32,
  maximum_retries: u8,
  magic_version: u16,
  unify: bool,
}

impl Default for ArenaOptions {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl ArenaOptions {
  /// Create an options for creating an ARENA with default values.
  #[inline]
  pub const fn new() -> Self {
    Self {
      maximum_alignment: 8,
      capacity: 1024,
      minimum_segment_size: 20,
      maximum_retries: 5,
      unify: false,
      magic_version: 0,
    }
  }

  /// Set the maximum alignment of the ARENA.
  ///
  /// If you are trying to allocate a `T` which requires a larger alignment than this value,
  /// then will lead to `read_unaligned`, which is undefined behavior on some platforms.
  ///
  /// The alignment must be a power of 2.
  /// The default maximum alignment is `8`.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_maximum_alignment(16);
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

  /// Set the capacity of the ARENA. This configuration will be ignored if the ARENA is backed by a memory map,
  /// see [`Arena::map_mut`](crate::alloc::Arena::map_mut), [`Arena::map`](crate::alloc::Arena::map) and [`Arena::map_anon`](crate::alloc::Arena::map_anon) for more details.
  ///
  /// The capacity must be greater than the minimum capacity of the ARENA.
  ///
  /// The default capacity is `1KB`.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_capacity(2048);
  /// ```
  #[inline]
  pub const fn with_capacity(mut self, capacity: u32) -> Self {
    self.capacity = capacity;
    self
  }

  /// Set the minimum segment size of the ARENA.
  ///
  /// This value controls the size of the holes.
  ///
  /// The default minimum segment size is `48 bytes`.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_minimum_segment_size(64);
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
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_maximum_retries(10);
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
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_unify(true);
  /// ```
  #[inline]
  pub const fn with_unify(mut self, unify: bool) -> Self {
    self.unify = unify;
    self
  }

  /// Set the external version of the ARENA,
  /// this is used by the application using [`Arena`](crate::Arena)
  /// to ensure that it doesn't open the [`Arena`](crate::Arena)
  /// with incompatible data format.
  ///
  /// The default value is `0`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_magic_version(1);
  /// ```
  #[inline]
  pub const fn with_magic_version(mut self, magic_version: u16) -> Self {
    self.magic_version = magic_version;
    self
  }

  /// Get the maximum alignment of the ARENA.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_maximum_alignment(16);
  ///
  /// assert_eq!(opts.maximum_alignment(), 16);
  /// ```
  #[inline]
  pub const fn maximum_alignment(&self) -> usize {
    self.maximum_alignment
  }

  /// Get the capacity of the ARENA.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_capacity(2048);
  ///
  /// assert_eq!(opts.capacity(), 2048);
  /// ```
  #[inline]
  pub const fn capacity(&self) -> u32 {
    self.capacity
  }

  /// Get the minimum segment size of the ARENA.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_minimum_segment_size(64);
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
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_maximum_retries(10);
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
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_unify(true);
  ///
  /// assert_eq!(opts.unify(), true);
  /// ```
  #[inline]
  pub const fn unify(&self) -> bool {
    self.unify
  }

  /// Get the external version of the ARENA,
  /// this is used by the application using [`Arena`](crate::Arena)
  /// to ensure that it doesn't open the [`Arena`](crate::Arena)
  /// with incompatible data format.
  ///
  /// The default value is `0`.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_magic_version(1);
  ///
  /// assert_eq!(opts.magic_version(), 1);
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.magic_version
  }
}
