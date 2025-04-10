#![no_std]
extern crate alloc;

mod unsigned;

#[allow(non_camel_case_types)]
pub type u2 = unsigned::u2;
#[allow(non_camel_case_types)]
pub type u4 = unsigned::u4;

pub trait ToSliceUnit<T, const N: usize> {
    fn to_slice_unit(&self) -> [T; N];
}