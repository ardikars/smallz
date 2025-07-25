#![cfg_attr(not(test), no_std)]
#![forbid(unsafe_code)]
extern crate alloc;

mod unsigned;

#[allow(non_camel_case_types)]
pub type u2 = unsigned::u2;
#[allow(non_camel_case_types)]
pub type u4 = unsigned::u4;

pub const U2_MIN_AS_U4: u4 = unsigned::U2_MIN_AS_U4;
pub const U2_MAX_AS_U4: u4 = unsigned::U2_MAX_AS_U4;
pub const U2_BITS_AS_U4: u4 = unsigned::U2_BITS_AS_U4;
