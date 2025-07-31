//#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;

mod unsigned;

#[allow(non_camel_case_types)]
pub type u2 = unsigned::u2;
#[allow(non_camel_case_types)]
pub type u4 = unsigned::u4;

pub const U2_MIN_AS_U4: u4 = unsigned::U2_MIN_AS_U4;
pub const U2_MAX_AS_U4: u4 = unsigned::U2_MAX_AS_U4;
pub const U2_BITS_AS_U4: u4 = unsigned::U2_BITS_AS_U4;

pub trait Convert {
    fn from_u2s_le(slice: &[u2]) -> Vec<u8>;
    fn from_u2s_be(slice: &[u2]) -> Vec<u8>;
    fn from_u2s_ne(slice: &[u2]) -> Vec<u8>;
    fn from_u4s_le(slice: &[u4]) -> Vec<u8>;
    fn from_u4s_be(slice: &[u4]) -> Vec<u8>;
    fn from_u4s_ne(slice: &[u4]) -> Vec<u8>;
}

impl Convert for Vec<u8> {
    fn from_u2s_le(slice: &[u2]) -> Vec<u8> {
        let slice_len = slice.len();
        let len = (slice_len / 4) + if slice_len.is_multiple_of(4) { 0 } else { 1 };
        let mut bytes = vec![0_u8; len];
        for (byte, chunks) in bytes.iter_mut().zip(slice.chunks(4)) {
            for chunk in chunks.iter().rev() {
                *byte <<= u2::BITS;
                *byte |= u8::from(*chunk);
            }
        }
        if let Some(keep) = bytes.iter().rposition(|&d| d != 0) {
            bytes[..keep + 1].to_vec()
        } else {
            Vec::new()
        }
    }

    fn from_u2s_be(slice: &[u2]) -> Vec<u8> {
        let slice_len = slice.len();
        let len = (slice_len / 4) + if slice_len.is_multiple_of(4) { 0 } else { 1 };
        let mut bytes = vec![0_u8; len];
        for (byte, chunks) in bytes.iter_mut().rev().zip(slice.rchunks(4)) {
            for chunk in chunks.iter() {
                *byte <<= u2::BITS;
                *byte |= u8::from(*chunk);
            }
        }
        if let Some(keep) = bytes.iter().position(|&d| d != 0) {
            bytes[keep..].to_vec()
        } else {
            Vec::new()
        }
    }

    fn from_u2s_ne(slice: &[u2]) -> Vec<u8> {
        #[cfg(target_endian = "little")]
        let v = Vec::from_u2s_le(slice);
        #[cfg(target_endian = "big")]
        let v = Vec::from_u2s_be(slice);
        v
    }

    fn from_u4s_le(slice: &[u4]) -> Vec<u8> {
        let slice_len = slice.len();
        let len = (slice_len / 2) + if slice_len.is_multiple_of(2) { 0 } else { 1 };
        let mut bytes = vec![0_u8; len];
        for (byte, chunks) in bytes.iter_mut().zip(slice.chunks(2)) {
            for chunk in chunks.iter().rev() {
                *byte <<= u4::BITS;
                *byte |= u8::from(*chunk);
            }
        }
        if let Some(keep) = bytes.iter().rposition(|&d| d != 0) {
            bytes[..keep + 1].to_vec()
        } else {
            Vec::new()
        }
    }

    fn from_u4s_be(slice: &[u4]) -> Vec<u8> {
        let slice_len = slice.len();
        let len = (slice_len / 2) + if slice_len.is_multiple_of(2) { 0 } else { 1 };
        let mut bytes = vec![0_u8; len];
        for (byte, chunks) in bytes.iter_mut().rev().zip(slice.rchunks(2)) {
            for chunk in chunks.iter() {
                *byte <<= u4::BITS;
                *byte |= u8::from(*chunk);
            }
        }
        if let Some(keep) = bytes.iter().position(|&d| d != 0) {
            bytes[keep..].to_vec()
        } else {
            Vec::new()
        }
    }

    fn from_u4s_ne(slice: &[u4]) -> Vec<u8> {
        #[cfg(target_endian = "little")]
        let v = Vec::from_u4s_le(slice);
        #[cfg(target_endian = "big")]
        let v = Vec::from_u4s_be(slice);
        v
    }
}

#[cfg(test)]
mod tests {
    use crate::{u2, u4, Convert};

    #[test]
    fn test_from_u2s_le_0() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        let u2s = &[zero, one, two, three, three, two, one];
        let bytes_be = Vec::from_u2s_be(u2s);
        assert_eq!(2, bytes_be.len());
        assert_eq!(vec![6, 249], bytes_be);

        let u2s = &[one, two, three, three, two, one, zero];
        let bytes_le = Vec::from_u2s_le(u2s);
        assert_eq!(2, bytes_le.len());
        assert_eq!(vec![249, 6], bytes_le);
    }

    #[test]
    fn test_from_u2s_le_1() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let u2s = &[zero, one];
        let bytes_be = Vec::from_u2s_be(u2s);
        assert_eq!(1, bytes_be.len());
        assert_eq!(vec![1], bytes_be);

        let u2s = &[one, zero];
        let bytes_le = Vec::from_u2s_le(u2s);
        assert_eq!(1, bytes_le.len());
        assert_eq!(vec![1], bytes_le);
    }

    #[test]
    fn test_from_u2s_le_2() {
        let zero = u2::try_from(0_u8).unwrap();
        let u2s = &[zero];
        let bytes_be = Vec::from_u2s_be(u2s);
        assert_eq!(0, bytes_be.len());
        assert_eq!(Vec::<u8>::new(), bytes_be);

        let u2s = &[zero];
        let bytes_le = Vec::from_u2s_le(u2s);
        assert_eq!(0, bytes_le.len());
        assert_eq!(Vec::<u8>::new(), bytes_le);
    }

    #[test]
    fn test_from_u2s_ne() {
        let zero = u2::try_from(0_u8).unwrap();
        let u2s = &[zero];
        let bytes_be = Vec::from_u2s_ne(u2s);
        assert_eq!(0, bytes_be.len());
        assert_eq!(Vec::<u8>::new(), bytes_be);

        let u2s = &[zero];
        let bytes_le = Vec::from_u2s_ne(u2s);
        assert_eq!(0, bytes_le.len());
        assert_eq!(Vec::<u8>::new(), bytes_le);
    }

    #[test]
    fn test_from_u4s_le_0() {
        let zero = u4::try_from(0_u8).unwrap();
        let one = u4::try_from(1_u8).unwrap();
        let two = u4::try_from(2_u8).unwrap();
        let three = u4::try_from(3_u8).unwrap();
        let u4s = &[zero, one, two, three, three, two, one];
        let bytes_be = Vec::from_u4s_be(u4s);
        assert_eq!(3, bytes_be.len());
        assert_eq!(vec![18, 51, 33], bytes_be);

        let u2s = &[one, two, three, three, two, one, zero];
        let bytes_le = Vec::from_u4s_le(u2s);
        assert_eq!(3, bytes_le.len());
        assert_eq!(vec![33, 51, 18], bytes_le);
    }

    #[test]
    fn test_from_u4s_le_1() {
        let zero = u4::try_from(0_u8).unwrap();
        let one = u4::try_from(1_u8).unwrap();
        let u4s = &[zero, one];
        let bytes_be = Vec::from_u4s_be(u4s);
        assert_eq!(1, bytes_be.len());
        assert_eq!(vec![1], bytes_be);

        let u4s = &[one, zero];
        let bytes_le = Vec::from_u4s_le(u4s);
        assert_eq!(1, bytes_le.len());
        assert_eq!(vec![1], bytes_le);
    }

    #[test]
    fn test_from_u4s_le_2() {
        let zero = u4::try_from(0_u8).unwrap();
        let u4s = &[zero];
        let bytes_be = Vec::from_u4s_be(u4s);
        assert_eq!(0, bytes_be.len());
        assert_eq!(Vec::<u8>::new(), bytes_be);

        let u4s = &[zero];
        let bytes_le = Vec::from_u4s_le(u4s);
        assert_eq!(0, bytes_le.len());
        assert_eq!(Vec::<u8>::new(), bytes_le);
    }

    #[test]
    fn test_from_u4s_3() {
        let zero = u4::try_from(0_u8).unwrap();
        let one = u4::try_from(1_u8).unwrap();
        let u4s = &[one, zero, zero];
        let bytes_be = Vec::from_u4s_be(u4s);
        assert_eq!(2, bytes_be.len());
        assert_eq!(vec![1, 0], bytes_be);

        let u4s = &[zero, zero, one];
        let bytes_le = Vec::from_u4s_le(u4s);
        assert_eq!(2, bytes_le.len());
        assert_eq!(vec![0, 1], bytes_le);
    }

    #[test]
    fn test_from_u4s_ne() {
        let zero = u4::try_from(0_u8).unwrap();
        let u4s = &[zero];
        let bytes_be = Vec::from_u4s_ne(u4s);
        assert_eq!(0, bytes_be.len());
        assert_eq!(Vec::<u8>::new(), bytes_be);

        let u4s = &[zero];
        let bytes_le = Vec::from_u4s_ne(u4s);
        assert_eq!(0, bytes_le.len());
        assert_eq!(Vec::<u8>::new(), bytes_le);
    }

    #[test]
    fn test_from_u2s_ne_fuzz_01() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let u2s = &[zero, zero, zero, zero, one];
        let bytes_le = Vec::from_u2s_le(u2s);
        assert_eq!(vec![0, 1], bytes_le);

        let u2s = &[one, zero, zero, zero, zero];
        let bytes_be = Vec::from_u2s_be(u2s);
        assert_eq!(vec![1, 0], bytes_be);
    }

    #[test]
    fn test_from_u4s_ne_fuzz_01() {
        let zero = u4::try_from(0_u8).unwrap();
        let one = u4::try_from(1_u8).unwrap();
        let u4s = &[zero, zero, zero, zero, one];
        let bytes_le = Vec::from_u4s_le(u4s);
        assert_eq!(vec![0, 0, 1], bytes_le);

        let u4s = &[one, zero, zero, zero, zero];
        let bytes_be = Vec::from_u4s_be(u4s);
        assert_eq!(vec![1, 0, 0], bytes_be);
    }
}
