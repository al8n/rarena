use memmap2::MmapOptions;
use std::fs::OpenOptions;

use super::ArenaOptions;

impl ArenaOptions {
  /// Sets the option for read access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `read`-able if opened.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_read(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_read(mut self, read: bool) -> Self {
    self.read = read;
    self
  }

  /// Sets the option for write access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `write`-able if opened.
  ///
  /// If the file already exists, any write calls on it will overwrite its
  /// contents, without truncating it.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_write(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_write(mut self, write: bool) -> Self {
    self.write = write;
    self
  }

  /// Sets the option for the append mode.
  ///
  /// This option, when true, means that writes will append to a file instead
  /// of overwriting previous contents.
  /// Note that setting `.write(true).append(true)` has the same effect as
  /// setting only `.append(true)`.
  ///
  /// For most filesystems, the operating system guarantees that all writes are
  /// atomic: no writes get mangled because another process writes at the same
  /// time.
  ///
  /// One maybe obvious note when using append-mode: make sure that all data
  /// that belongs together is written to the file in one operation. This
  /// can be done by concatenating strings before passing them to [`write()`],
  /// or using a buffered writer (with a buffer of adequate size),
  /// and calling [`flush()`] when the message is complete.
  ///
  /// If a file is opened with both read and append access, beware that after
  /// opening, and after every write, the position for reading may be set at the
  /// end of the file. So, before writing, save the current position (using
  /// <code>[seek]\([SeekFrom](std::io::SeekFrom)::[Current]\(opts))</code>), and restore it before the next read.
  ///
  /// ## Note
  ///
  /// This function doesn't create the file if it doesn't exist. Use the
  /// [`OpenOptions::create`] method to do so.
  ///
  /// [`write()`]: std::io::Write::write "io::Write::write"
  /// [`flush()`]: std::io::Write::flush "io::Write::flush"
  /// [seek]: std::io::Seek::seek "io::Seek::seek"
  /// [Current]: std::io::SeekFrom::Current "io::SeekFrom::Current"
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_append(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_append(mut self, append: bool) -> Self {
    self.write = true;
    self.append = append;
    self
  }

  /// Sets the option for truncating a previous file.
  ///
  /// If a file is successfully opened with this option set it will truncate
  /// the file to opts length if it already exists.
  ///
  /// The file must be opened with write access for truncate to work.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_write(true).with_truncate(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_truncate(mut self, truncate: bool) -> Self {
    self.truncate = truncate;
    self.write = true;
    self
  }

  /// Sets the option to create a new file, or open it if it already exists.
  /// If the file does not exist, it is created and set the lenght of the file to the given size.
  ///
  /// In order for the file to be created, [`OpenOptions::write`] or
  /// [`OpenOptions::append`] access must be used.
  ///
  /// See also [`std::fs::write()`][std::fs::write] for a simple function to
  /// create a file with some given data.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().write(true).with_create(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_create(mut self, val: bool) -> Self {
    self.create = val;
    self
  }

  /// Sets the option to create a new file and set the file length to the given value, failing if it already exists.
  ///
  /// No file is allowed to exist at the target location, also no (dangling) symlink. In this
  /// way, if the call succeeds, the file returned is guaranteed to be new.
  ///
  /// This option is useful because it is atomic. Otherwise between checking
  /// whether a file exists and creating a new one, the file may have been
  /// created by another process (a TOCTOU race condition / attack).
  ///
  /// If `.create_new(true)` is set, [`.create()`] and [`.truncate()`] are
  /// ignored.
  ///
  /// The file must be opened with write or append access in order to create
  /// a new file.
  ///
  /// [`.create()`]: OpenOptions::create
  /// [`.truncate()`]: OpenOptions::truncate
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let file = ArenaOptions::new()
  ///   .write(true)
  ///   .with_create_new(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_create_new(mut self, val: bool) -> Self {
    self.create_new = val;
    self
  }

  /// Configures the memory map to start at byte `offset` from the beginning of the file.
  ///
  /// This option has no effect on anonymous memory maps or vec backed [`Allocator`](crate::Allocator).
  ///
  /// By default, the offset is 0.
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_offset(30);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_offset(mut self, offset: u64) -> Self {
    self.offset = offset;
    self
  }

  /// Configures the anonymous memory map to be suitable for a process or thread stack.
  ///
  /// This option corresponds to the `MAP_STACK` flag on Linux. It has no effect on Windows.
  ///
  /// This option has no effect on file-backed memory maps and vec backed [`Allocator`](crate::Allocator).
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let stack = ArenaOptions::new().with_stack(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_stack(mut self, stack: bool) -> Self {
    self.stack = stack;
    self
  }

  /// Configures the anonymous memory map to be allocated using huge pages.
  ///
  /// This option corresponds to the `MAP_HUGETLB` flag on Linux. It has no effect on Windows.
  ///
  /// The size of the requested page can be specified in page bits. If not provided, the system
  /// default is requested. The requested length should be a multiple of this, or the mapping
  /// will fail.
  ///
  /// This option has no effect on file-backed memory maps and vec backed [`Allocator`](crate::Allocator).
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let stack = ArenaOptions::new().with_huge(Some(8));
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_huge(mut self, page_bits: Option<u8>) -> Self {
    self.huge = page_bits;
    self
  }

  /// Populate (prefault) page tables for a mapping.
  ///
  /// For a file mapping, this causes read-ahead on the file. This will help to reduce blocking on page faults later.
  ///
  /// This option corresponds to the `MAP_POPULATE` flag on Linux. It has no effect on Windows.
  ///
  /// This option has no effect on vec backed [`Allocator`](crate::Allocator).
  ///
  /// ## Example
  ///
  /// ```
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_populate(true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn with_populate(mut self, populate: bool) -> Self {
    self.populate = populate;
    self
  }
}

impl ArenaOptions {
  /// Returns `true` if the file should be opened with read access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_read(true);
  /// assert_eq!(opts.read(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn read(&self) -> bool {
    self.read
  }

  /// Returns `true` if the file should be opened with write access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_write(true);
  /// assert_eq!(opts.write(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn write(&self) -> bool {
    self.write
  }

  /// Returns `true` if the file should be opened with append access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_append(true);
  /// assert_eq!(opts.append(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn append(&self) -> bool {
    self.append
  }

  /// Returns `true` if the file should be opened with truncate access.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_truncate(true);
  /// assert_eq!(opts.truncate(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn truncate(&self) -> bool {
    self.truncate
  }

  /// Returns `true` if the file should be created if it does not exist.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_create(true);
  /// assert_eq!(opts.create(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn create(&self) -> bool {
    self.create
  }

  /// Returns `true` if the file should be created if it does not exist and fail if it does.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_create_new(true);
  /// assert_eq!(opts.create_new(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn create_new(&self) -> bool {
    self.create_new
  }

  /// Returns the offset of the memory map.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_offset(30);
  /// assert_eq!(opts.offset(), 30);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn offset(&self) -> u64 {
    self.offset
  }

  /// Returns `true` if the memory map should be suitable for a process or thread stack.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_stack(true);
  /// assert_eq!(opts.stack(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn stack(&self) -> bool {
    self.stack
  }

  /// Returns the page bits of the memory map.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_huge(Some(8));
  /// assert_eq!(opts.huge(), Some(8));
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn huge(&self) -> Option<u8> {
    self.huge
  }

  /// Returns `true` if the memory map should populate (prefault) page tables for a mapping.
  ///
  /// ## Examples
  ///
  /// ```rust
  /// use rarena_allocator::ArenaOptions;
  ///
  /// let opts = ArenaOptions::new().with_populate(true);
  /// assert_eq!(opts.populate(), true);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub const fn populate(&self) -> bool {
    self.populate
  }
}

impl From<&ArenaOptions> for MmapOptions {
  fn from(opts: &ArenaOptions) -> Self {
    let mut mmap_opts = MmapOptions::new();

    if opts.stack() {
      mmap_opts.stack();
    }

    if let Some(page_bits) = opts.huge() {
      mmap_opts.huge(Some(page_bits));
    }

    if opts.populate() {
      mmap_opts.populate();
    }

    let offset = opts.offset();
    if offset > 0 {
      mmap_opts.offset(offset);
    }

    let cap = opts.capacity();
    if cap > 0 {
      mmap_opts.len(cap as usize);
    }

    mmap_opts
  }
}

impl From<ArenaOptions> for OpenOptions {
  fn from(opts: ArenaOptions) -> Self {
    let mut open_opts = OpenOptions::new();

    if opts.read() {
      open_opts.read(true);
    }

    if opts.write() {
      open_opts.write(true);
    }

    if opts.append() {
      open_opts.append(true);
    }

    if opts.truncate() {
      open_opts.truncate(true);
    }

    if opts.create() {
      open_opts.create(true);
    }

    if opts.create_new() {
      open_opts.create_new(true);
    }

    open_opts
  }
}
