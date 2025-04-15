#![no_std]
#![forbid(unsafe_code)]
extern crate alloc;

mod unsigned;

#[allow(non_camel_case_types)]
pub type u2 = unsigned::u2;
#[allow(non_camel_case_types)]
pub type u4 = unsigned::u4;
