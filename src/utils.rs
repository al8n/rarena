
/// Returns a bitmask containing the unused least significant bits of an aligned pointer to `T`.
#[inline]
const fn low_bits<T>() -> usize {
  (1 << core::mem::align_of::<T>().trailing_zeros()) - 1
}

/// Given a tagged pointer `data`, returns the same pointer, but tagged with `tag`.
///
/// `tag` is truncated to fit into the unused bits of the pointer to `T`.
#[inline]
pub(crate) fn compose_tag<T>(ptr: *mut (), tag: usize) -> *mut () {
  int_to_ptr_with_provenance(
    (ptr as usize & !low_bits::<T>()) | (tag & low_bits::<T>()),
    ptr,
  )
}

/// Decomposes a tagged pointer `data` into the pointer and the tag.
#[inline]
pub(crate) fn decompose_tag<T>(ptr: *mut ()) -> (*mut (), usize) {
  (
    int_to_ptr_with_provenance(ptr as usize & !low_bits::<T>(), ptr),
    ptr as usize & low_bits::<T>(),
  )
}

// HACK: https://github.com/rust-lang/miri/issues/1866#issuecomment-985802751
#[inline]
fn int_to_ptr_with_provenance<T>(addr: usize, prov: *mut T) -> *mut T {
  let ptr = prov.cast::<u8>();
  ptr.wrapping_add(addr.wrapping_sub(ptr as usize)).cast()
}
