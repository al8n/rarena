use memmap2::MmapOptions;
use std::{
  fs::{File, OpenOptions},
  io,
  path::Path,
};

use super::{Allocator, ArenaOptions};

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

impl ArenaOptions {
  /// Creates a new allocator backed by an anonymous mmap.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = ArenaOptions::new().with_capacity(100).map_anon::<Arena>().unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub fn map_anon<A: Allocator>(self) -> std::io::Result<A> {
    constructor!(self.map_anon())
  }

  /// Opens a read only allocator backed by a mmap file.
  ///
  /// ## Safety
  ///
  /// All file-backed memory map constructors are marked `unsafe` because of the potential for
  /// *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  /// out of process. Applications must consider the risk and take appropriate precautions when
  /// using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  /// unlinked) files exist but are platform specific and limited.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// # {
  /// #   let arena = unsafe {  ArenaOptions::new().with_capacity(100).with_create_new(true).with_read(true).with_write(true).map_mut::<Arena, _>(&path).unwrap() };
  /// # }
  ///
  /// let open_options = OpenOptions::default().read(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = unsafe { ArenaOptions::new().map::<Arena, _>(&path,).unwrap() };
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub unsafe fn map<A: Allocator, P: AsRef<std::path::Path>>(self, p: P) -> std::io::Result<A> {
    constructor!(self.map(p))
  }

  /// Opens a read only allocator backed by a mmap file with the given path builder.
  ///
  /// ## Safety
  ///
  /// All file-backed memory map constructors are marked `unsafe` because of the potential for
  /// *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  /// out of process. Applications must consider the risk and take appropriate precautions when
  /// using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  /// unlinked) files exist but are platform specific and limited.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Allocator, ArenaOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// # {
  /// #   let arena = unsafe { ArenaOptions::new().with_capacity(100).with_read(true).with_write(true).with_create_new(true).map_mut::<Arena, _>(&path).unwrap() };
  /// # }
  ///
  /// let open_options = OpenOptions::default().read(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = unsafe { ArenaOptions::new().map_with_path_builder::<Arena, _, std::io::Error>(|| Ok(path.to_path_buf()),).unwrap() };
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub unsafe fn map_with_path_builder<A: Allocator, PB, E>(
    self,
    path_builder: PB,
  ) -> Result<A, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    constructor!(self.map_with_path_builder(path_builder))
  }

  /// Creates a new allocator backed by a copy-on-write memory map backed by a file.
  ///
  /// Data written to the allocator will not be visible by other processes, and will not be carried through to the underlying file.
  ///
  /// ## Safety
  ///
  /// All file-backed memory map constructors are marked `unsafe` because of the potential for
  /// *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  /// out of process. Applications must consider the risk and take appropriate precautions when
  /// using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  /// unlinked) files exist but are platform specific and limited.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let arena = unsafe { ArenaOptions::new().with_capacity(100).with_read(true).with_write(true).with_create_new(true).map_copy::<Arena, _>(&path,).unwrap() };
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_copy<A: Allocator, P: AsRef<std::path::Path>>(
    self,
    path: P,
  ) -> std::io::Result<A> {
    constructor!(self.map_copy(path))
  }

  /// Creates a new allocator backed by a copy-on-write memory map backed by a file with the given path builder.
  ///
  /// Data written to the allocator will not be visible by other processes, and will not be carried through to the underlying file.
  ///
  /// ## Safety
  ///
  /// All file-backed memory map constructors are marked `unsafe` because of the potential for
  /// *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  /// out of process. Applications must consider the risk and take appropriate precautions when
  /// using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  /// unlinked) files exist but are platform specific and limited.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let arena = unsafe { ArenaOptions::new().with_capacity(100).with_create_new(true).with_read(true).with_write(true).map_copy_with_path_builder::<Arena, _, std::io::Error>(|| Ok(path.to_path_buf()),).unwrap() };
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_copy_with_path_builder<A: Allocator, PB, E>(
    self,
    path_builder: PB,
  ) -> Result<A, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    constructor!(self.map_copy_with_path_builder(path_builder))
  }

  /// Opens a read only allocator backed by a copy-on-write read-only memory map backed by a file.
  ///
  /// ## Safety
  ///
  /// All file-backed memory map constructors are marked `unsafe` because of the potential for
  /// *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  /// out of process. Applications must consider the risk and take appropriate precautions when
  /// using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  /// unlinked) files exist but are platform specific and limited.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// # {
  /// #   let arena = unsafe {  ArenaOptions::new().with_capacity(100).with_create_new().with_read(true).with_write(true).map_mut::<Arena, _>(&path).unwrap() };
  /// # }
  ///
  /// let open_options = OpenOptions::default().read(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = unsafe { ArenaOptions::new().map_copy_read_only::<Arena, _>(&path,).unwrap() };
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_copy_read_only<A: Allocator, P: AsRef<std::path::Path>>(
    self,
    path: P,
  ) -> std::io::Result<A> {
    constructor!(self.map_copy_read_only(path))
  }

  /// Opens a read only allocator backed by a copy-on-write read-only memory map backed by a file with the given path builder.
  ///
  /// ## Safety
  ///
  /// All file-backed memory map constructors are marked `unsafe` because of the potential for
  /// *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  /// out of process. Applications must consider the risk and take appropriate precautions when
  /// using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  /// unlinked) files exist but are platform specific and limited.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// # {
  ///   # let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  ///   # let mmap_options = MmapOptions::new();
  ///   # let arena = unsafe { ArenaOptions::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut(&path).unwrap() };
  /// # }
  ///
  /// let open_options = OpenOptions::default().read(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = unsafe {
  ///   ArenaOptions::new().map_copy_read_only_with_path_builder::<Arena, _, std::io::Error>(|| Ok(path.to_path_buf())).unwrap()
  /// };
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub unsafe fn map_copy_read_only_with_path_builder<A: Allocator, PB, E>(
    self,
    path_builder: PB,
  ) -> Result<A, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    constructor!(self.map_copy_read_only_with_path_builder(path_builder))
  }

  /// Creates a new allocator backed by a mmap with the given path.
  ///
  /// ## Safety
  ///
  /// All file-backed memory map constructors are marked `unsafe` because of the potential for
  /// *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  /// out of process. Applications must consider the risk and take appropriate precautions when
  /// using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  /// unlinked) files exist but are platform specific and limited.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let arena = unsafe {
  ///   ArenaOptions::new()
  ///     .with_capacity(100)
  ///     .with_create_new(true)
  ///     .with_read(true)
  ///     .with_write(true)
  ///     .map_mut::<Arena, _>(&path).unwrap()
  /// };
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub unsafe fn map_mut<A: Allocator, P: AsRef<std::path::Path>>(
    self,
    path: P,
  ) -> std::io::Result<A> {
    constructor!(self.map_mut(path))
  }

  /// Creates a new allocator backed by a mmap with the given path builder.
  ///
  /// ## Safety
  ///
  /// All file-backed memory map constructors are marked `unsafe` because of the potential for
  /// *Undefined Behavior* (UB) using the map if the underlying file is subsequently modified, in or
  /// out of process. Applications must consider the risk and take appropriate precautions when
  /// using file-backed maps. Solutions such as file permissions, locks or process-private (e.g.
  /// unlinked) files exist but are platform specific and limited.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let arena = unsafe {
  ///   ArenaOptions::new()
  ///     .with_create_new(true)
  ///     .with_read(true)
  ///     .with_write(true)
  ///     .with_capacity(100)
  ///     .map_mut_with_path_builder::<Arena, _, std::io::Error>(|| Ok(path.to_path_buf())).unwrap()
  /// };
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub unsafe fn map_mut_with_path_builder<A: Allocator, PB, E>(
    self,
    path_builder: PB,
  ) -> Result<A, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    constructor!(self.map_mut_with_path_builder(path_builder))
  }
}

impl ArenaOptions {
  pub(crate) fn open<P: AsRef<Path>>(&self, path: P) -> io::Result<(bool, File)> {
    if self.create_new {
      return self
        .to_open_options()
        .open(path)
        .and_then(|f| f.set_len(self.capacity as u64).map(|_| (true, f)));
    }

    if self.create {
      return if path.as_ref().exists() {
        self.to_open_options().open(path).map(|f| (false, f))
      } else {
        self
          .to_open_options()
          .open(path)
          .and_then(|f| f.set_len(self.capacity as u64).map(|_| (true, f)))
      };
    }

    self.to_open_options().open(path).map(|f| (false, f))
  }

  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(crate) fn to_open_options(&self) -> OpenOptions {
    let mut open_opts = OpenOptions::new();

    if self.read {
      open_opts.read(true);
    }

    if self.write {
      open_opts.write(true);
    }

    if self.append {
      open_opts.append(true);
    }

    if self.truncate {
      open_opts.truncate(true);
    }

    if self.create {
      open_opts.create(true);
    }

    if self.create_new {
      open_opts.create_new(true);
    }

    open_opts
  }

  #[allow(clippy::wrong_self_convention)]
  #[inline]
  pub(crate) fn to_mmap_options(&self) -> MmapOptions {
    let mut mmap_opts = MmapOptions::new();

    if self.stack {
      mmap_opts.stack();
    }

    if let Some(page_bits) = self.huge {
      mmap_opts.huge(Some(page_bits));
    }

    if self.populate {
      mmap_opts.populate();
    }

    if self.offset > 0 {
      mmap_opts.offset(self.offset);
    }

    if self.capacity > 0 {
      mmap_opts.len(self.capacity as usize);
    }

    mmap_opts
  }
}
