#![allow(dead_code)]

use super::*;

common_unit_tests!("unsync": Arena {
  type Header = crate::unsync::sealed::Header;
  type SegmentNode = super::SegmentNode;
});

#[test]
fn test_meta_eq() {
  let a_ptr = 1u8;
  let b_ptr = 1u8;
  let a = Meta::new(&a_ptr as _, 2, 3);
  let b = Meta::new(&b_ptr as _, 2, 3);
  assert_ne!(a, b);
}
