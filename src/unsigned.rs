extern crate alloc;

use alloc::fmt;
use alloc::format;
use alloc::string::String;
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

macro_rules! unsigned {
    ($name:ident, $bits:tt, $slice:tt) => {
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
        pub struct $name(u8);

        impl $name {
            const MASK: u8 = (1 << $bits) - 1;

            pub const BITS: u32 = $bits;
            pub const ZERO: $name = $name(0);
            pub const ONE: $name = $name(1);
            pub const MIN: $name = $name(0);
            pub const MAX: $name = $name(Self::MASK);

            pub fn from_exact(byte: u8) -> [$name; $slice] {
                let mut v: [$name; $slice] = [$name(0); $slice];
                let mut b: u8 = u8::BITS as u8;
                for i in 0..$slice {
                    b -= $bits;
                    v[i] = $name((byte >> b) & Self::MASK);
                }
                v
            }

            pub fn leading_zeros(&self) -> u32 {
                self.0.leading_zeros() - (u8::BITS - Self::BITS)
            }

            pub fn trailing_zeros(&self) -> u32 {
                let zeros = self.0.trailing_zeros();
                if zeros > Self::BITS {
                    Self::BITS
                } else {
                    zeros
                }
            }

            pub fn bit_len(&self) -> u32 {
                Self::BITS - self.leading_zeros()
            }

            pub fn to_str_radix(self, radix: usize) -> String {
                if radix == 2 {
                    format!("{:0width$b}", self.0, width = Self::BITS as usize)
                } else if radix == 8 {
                    format!("{:o}", self.0)
                } else if radix == 10 {
                    format!("{}", self.0)
                } else if radix == 16 {
                    format!("{:x}", self.0)
                } else {
                    panic!("unsupported radix")
                }
            }
        }

        impl TryFrom<u8> for $name {
            type Error = String;
            fn try_from(value: u8) -> Result<Self, Self::Error> {
                if value > Self::MAX.0 {
                    Err(format!(
                        "value {} is out of range for {}",
                        value,
                        stringify!($name)
                    ))
                } else {
                    Ok($name(value))
                }
            }
        }

        impl From<$name> for u8 {
            fn from(value: $name) -> u8 {
                value.0 as u8
            }
        }

        impl TryFrom<u16> for $name {
            type Error = String;
            fn try_from(value: u16) -> Result<Self, Self::Error> {
                if value > Self::MAX.0 as u16 {
                    Err(format!(
                        "value {} is out of range for {}",
                        value,
                        stringify!($name)
                    ))
                } else {
                    Ok($name(value as u8))
                }
            }
        }

        impl From<$name> for u16 {
            fn from(value: $name) -> u16 {
                value.0 as u16
            }
        }

        impl TryFrom<u32> for $name {
            type Error = String;
            fn try_from(value: u32) -> Result<Self, Self::Error> {
                if value > Self::MAX.0 as u32 {
                    Err(format!(
                        "value {} is out of range for {}",
                        value,
                        stringify!($name)
                    ))
                } else {
                    Ok($name(value as u8))
                }
            }
        }

        impl From<$name> for u32 {
            fn from(value: $name) -> u32 {
                value.0 as u32
            }
        }

        impl TryFrom<u64> for $name {
            type Error = String;
            fn try_from(value: u64) -> Result<Self, Self::Error> {
                if value > Self::MAX.0 as u64 {
                    Err(format!(
                        "value {} is out of range for {}",
                        value,
                        stringify!($name)
                    ))
                } else {
                    Ok($name(value as u8))
                }
            }
        }

        impl From<$name> for u64 {
            fn from(value: $name) -> u64 {
                value.0 as u64
            }
        }

        impl TryFrom<u128> for $name {
            type Error = String;
            fn try_from(value: u128) -> Result<Self, Self::Error> {
                if value > Self::MAX.0 as u128 {
                    Err(format!(
                        "value {} is out of range for {}",
                        value,
                        stringify!($name)
                    ))
                } else {
                    Ok($name(value as u8))
                }
            }
        }

        impl From<$name> for u128 {
            fn from(value: $name) -> u128 {
                value.0 as u128
            }
        }

        impl From<usize> for $name {
            fn from(value: usize) -> $name {
                $name((value & (Self::MASK as usize)) as u8)
            }
        }

        impl From<$name> for usize {
            fn from(value: $name) -> usize {
                value.0 as usize
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.0)
            }
        }
    };
}

macro_rules! unsigned_op {
    ($trait:ident, $trait_assign:ident, $type:ty, $method:ident, $method_assign:ident, $op:tt) => {
        impl $trait for $type {
            type Output = $type;
            fn $method(self, rhs: $type) -> Self::Output {
                let r = self.0 $op rhs.0;
                if r > Self::MASK {
                    panic!("attempt to {} with overflow", stringify!($method));
                } else {
                    <$type>::try_from(r).unwrap()
                }
            }
        }

        impl $trait_assign for $type {
            fn $method_assign(&mut self, rhs: $type) {
                let r = self.0 $op rhs.0;
                if r > Self::MASK {
                    panic!("attempt to add with overflow");
                } else {
                    self.0 = r;
                }
            }
        }
    };
}

macro_rules! unsigned_shift_op {
    ($trait:ident, $trait_assign:ident, $type:ty, $method:ident, $method_assign:ident, $op:tt) => {
        impl $trait for $type {
            type Output = $type;
            fn $method(self, rhs: $type) -> Self::Output {
                if u32::from(rhs.0) < Self::BITS {
                    <$type>::try_from(self.0 $op rhs.0).unwrap()
                } else {
                    panic!("attempt to shift {} by `{}`, which would overflow", stringify!($op), rhs.0)
                }
            }
        }

        impl $trait_assign for $type {
            fn $method_assign(&mut self, rhs: $type) {
                if u32::from(rhs.0) < Self::BITS {
                    self.0 = self.0 $op rhs.0;
                } else {
                    panic!("attempt to shift {} by `{}`, which would overflow", stringify!($op), rhs.0);
                }
            }
        }
    };
}

macro_rules! unsigned_ops {
    ($type:ty) => {
        unsigned_op!(Add, AddAssign, $type, add, add_assign, +);
        unsigned_op!(Sub, SubAssign, $type, sub, sub_assign, -);
        unsigned_op!(Mul, MulAssign, $type, mul, mul_assign, *);
        unsigned_op!(Div, DivAssign, $type, div, div_assign, /);
        unsigned_op!(Rem, RemAssign, $type, rem, rem_assign, %);
        unsigned_op!(BitAnd, BitAndAssign, $type, bitand, bitand_assign, &);
        unsigned_op!(BitOr, BitOrAssign, $type, bitor, bitor_assign, |);
        unsigned_op!(BitXor, BitXorAssign, $type, bitxor, bitxor_assign, ^);
        unsigned_shift_op!(Shl, ShlAssign, $type, shl, shl_assign, <<);
        unsigned_shift_op!(Shr, ShrAssign, $type, shr, shr_assign, >>);

        impl Not for $type {
            type Output = $type;
            fn not(self) -> Self::Output {
                <$type>::try_from(!self.0).unwrap()
            }
        }
    };
}

macro_rules! unsigned_overflowing_op {
    ($type:ty, $method:ident, $op:tt) => {
        pub fn $method(&self, rhs: $type) -> ($type, bool) {
            let r = self.0 $op rhs.0;
            if r > Self::MASK {
                (<$type>::try_from(r - Self::MASK - 1).unwrap(), true)
            } else {
                (<$type>::try_from(r).unwrap(), false)
            }
        }
    }
}

macro_rules! unsigned_overflowing_ops {
    ($type:ty) => {
        impl $type {
            unsigned_overflowing_op!($type, overflowing_add, +);
            unsigned_overflowing_op!($type, overflowing_mul, *);

            pub fn overflowing_sub(&self, rhs: $type) -> ($type, bool) {
                if self.0 < rhs.0 {
                    (<$type>::try_from(Self::MASK - (rhs.0 - self.0) + 1).unwrap(), true)
                } else {
                    (<$type>::try_from(self.0 - rhs.0).unwrap(), false)
                }
            }
        }
    };
}

macro_rules! unsigned_wrapping_op {
    ($type:ty, $method:ident, $op:tt) => {
        pub fn $method(&self, rhs: $type) -> $type {
            <$type>::try_from(self.0 $op rhs.0).unwrap()
        }
    }
}

macro_rules! unsigned_wrapping_ops {
    ($type:ty) => {
        impl $type {
            unsigned_wrapping_op!($type, wrapping_add, +);
            unsigned_wrapping_op!($type, wrapping_mul, *);

            pub fn wrapping_sub(&self, rhs: $type) -> $type {
                if self.0 < rhs.0 {
                    <$type>::try_from(Self::MASK - (rhs.0 - self.0) + 1).unwrap()
                } else {
                    <$type>::try_from(self.0 - rhs.0).unwrap()
                }
            }
        }
    };
}

unsigned!(u2, 2, 4);
unsigned!(u4, 4, 2);

impl TryFrom<u4> for u2 {
    type Error = String;
    fn try_from(value: u4) -> Result<Self, Self::Error> {
        if value.0 > Self::MAX.0 {
            Err(format!("value {} is out of range for u2", value.0))
        } else {
            Ok(u2(value.0))
        }
    }
}

impl From<u2> for u4 {
    fn from(value: u2) -> u4 {
        u4(value.0)
    }
}

unsigned_ops!(u2);
unsigned_ops!(u4);

unsigned_overflowing_ops!(u2);
unsigned_overflowing_ops!(u4);
unsigned_wrapping_ops!(u2);
unsigned_wrapping_ops!(u4);

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use std::panic::catch_unwind;

    macro_rules! assert_panic {
        ($expr:expr) => {
            assert!(
                catch_unwind(|| $expr).is_err(),
                "Expected panic, but no panic occurred."
            );
        };
    }

    #[test]
    fn test_unsigned_from_base() {
        let slice = u4::from_exact(1);
        assert_eq!(slice[0], u4::try_from(0_u8).unwrap());
        assert_eq!(slice[1], u4::try_from(1_u8).unwrap());
        assert_eq!(slice.len(), 2);
        let slice = u4::from_exact(16);
        assert_eq!(slice[0], u4::try_from(1_u8).unwrap());
        assert_eq!(slice[1], u4::try_from(0_u8).unwrap());
        assert_eq!(slice.len(), 2);
    }

    #[test]
    fn test_unsigned_add_overflow() {
        assert_panic!(u2::try_from(1_u8).unwrap() + u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() + u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() + u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() + u2::try_from(1_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() + u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() + u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_overflowing_add() {
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_add(u2::try_from(3_u8).unwrap()), (u2::try_from(0_u8).unwrap(), true));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_add(u2::try_from(2_u8).unwrap()), (u2::try_from(0_u8).unwrap(), true));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_add(u2::try_from(3_u8).unwrap()), (u2::try_from(1_u8).unwrap(), true));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_add(u2::try_from(1_u8).unwrap()), (u2::try_from(0_u8).unwrap(), true));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_add(u2::try_from(2_u8).unwrap()), (u2::try_from(1_u8).unwrap(), true));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_add(u2::try_from(3_u8).unwrap()), (u2::try_from(2_u8).unwrap(), true));
        // not overflow
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_add(u2::try_from(0_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_add(u2::try_from(1_u8).unwrap()), (u2::try_from(1_u8).unwrap(), false));
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_add(u2::try_from(2_u8).unwrap()), (u2::try_from(2_u8).unwrap(), false));
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_add(u2::try_from(3_u8).unwrap()), (u2::try_from(3_u8).unwrap(), false));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_add(u2::try_from(0_u8).unwrap()), (u2::try_from(1_u8).unwrap(), false));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_add(u2::try_from(1_u8).unwrap()), (u2::try_from(2_u8).unwrap(), false));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_add(u2::try_from(2_u8).unwrap()), (u2::try_from(3_u8).unwrap(), false));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_add(u2::try_from(0_u8).unwrap()), (u2::try_from(2_u8).unwrap(), false));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_add(u2::try_from(1_u8).unwrap()), (u2::try_from(3_u8).unwrap(), false));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_add(u2::try_from(0_u8).unwrap()), (u2::try_from(3_u8).unwrap(), false));
    }

    #[test]
    fn test_unsigned_wrapping_add() {
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_add(u2::try_from(3_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_add(u2::try_from(2_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_add(u2::try_from(3_u8).unwrap()), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_add(u2::try_from(1_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_add(u2::try_from(2_u8).unwrap()), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_add(u2::try_from(3_u8).unwrap()), u2::try_from(2_u8).unwrap());
        // not overflow
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_add(u2::try_from(0_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_add(u2::try_from(1_u8).unwrap()), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_add(u2::try_from(2_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_add(u2::try_from(3_u8).unwrap()), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_add(u2::try_from(0_u8).unwrap()), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_add(u2::try_from(1_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_add(u2::try_from(2_u8).unwrap()), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_add(u2::try_from(0_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_add(u2::try_from(1_u8).unwrap()), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_add(u2::try_from(0_u8).unwrap()), u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_add() {
        assert_eq!(u2::try_from(0_u8).unwrap() + u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() + u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() + u2::try_from(2_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() + u2::try_from(3_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() + u2::try_from(0_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() + u2::try_from(1_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() + u2::try_from(2_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() + u2::try_from(0_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() + u2::try_from(1_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() + u2::try_from(0_u8).unwrap(), u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_sub_overflow() {
        assert_panic!(u2::try_from(0_u8).unwrap() - u2::try_from(1_u8).unwrap());
        assert_panic!(u2::try_from(0_u8).unwrap() - u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(0_u8).unwrap() - u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(1_u8).unwrap() - u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(1_u8).unwrap() - u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() - u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_overflowing_sub() {
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_sub(u2::try_from(1_u8).unwrap()), (u2::try_from(3_u8).unwrap(), true));
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_sub(u2::try_from(2_u8).unwrap()), (u2::try_from(2_u8).unwrap(), true));
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_sub(u2::try_from(3_u8).unwrap()), (u2::try_from(1_u8).unwrap(), true));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_sub(u2::try_from(2_u8).unwrap()), (u2::try_from(3_u8).unwrap(), true));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_sub(u2::try_from(3_u8).unwrap()), (u2::try_from(2_u8).unwrap(), true));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_sub(u2::try_from(3_u8).unwrap()), (u2::try_from(3_u8).unwrap(), true));
        // not overflow
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_sub(u2::try_from(0_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_sub(u2::try_from(0_u8).unwrap()), (u2::try_from(1_u8).unwrap(), false));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_sub(u2::try_from(1_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_sub(u2::try_from(0_u8).unwrap()), (u2::try_from(2_u8).unwrap(), false));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_sub(u2::try_from(1_u8).unwrap()), (u2::try_from(1_u8).unwrap(), false));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_sub(u2::try_from(2_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_sub(u2::try_from(0_u8).unwrap()), (u2::try_from(3_u8).unwrap(), false));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_sub(u2::try_from(1_u8).unwrap()), (u2::try_from(2_u8).unwrap(), false));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_sub(u2::try_from(2_u8).unwrap()), (u2::try_from(1_u8).unwrap(), false));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_sub(u2::try_from(3_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
    }

    #[test]
    fn test_unsigned_wrapping_sub() {
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_sub(u2::try_from(1_u8).unwrap()), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_sub(u2::try_from(2_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_sub(u2::try_from(3_u8).unwrap()), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_sub(u2::try_from(2_u8).unwrap()), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_sub(u2::try_from(3_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_sub(u2::try_from(3_u8).unwrap()), u2::try_from(3_u8).unwrap());
        // not overflow
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_sub(u2::try_from(0_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_sub(u2::try_from(0_u8).unwrap()), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_sub(u2::try_from(1_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_sub(u2::try_from(0_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_sub(u2::try_from(1_u8).unwrap()), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_sub(u2::try_from(2_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_sub(u2::try_from(0_u8).unwrap()), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_sub(u2::try_from(1_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_sub(u2::try_from(2_u8).unwrap()), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_sub(u2::try_from(3_u8).unwrap()), u2::try_from(0_u8).unwrap());
    }

    #[test]
    fn test_unsigned_sub() {
        assert_eq!(u2::try_from(0_u8).unwrap() - u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() - u2::try_from(0_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() - u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() - u2::try_from(0_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() - u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() - u2::try_from(2_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() - u2::try_from(0_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() - u2::try_from(1_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() - u2::try_from(2_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() - u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
    }

    #[test]
    fn test_unsigned_mul_overflow() {
        assert_panic!(u2::try_from(2_u8).unwrap() * u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() * u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() * u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() * u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_overflowing_mul() {
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_mul(u2::try_from(2_u8).unwrap()), (u2::try_from(0_u8).unwrap(), true));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_mul(u2::try_from(3_u8).unwrap()), (u2::try_from(2_u8).unwrap(), true));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_mul(u2::try_from(2_u8).unwrap()), (u2::try_from(2_u8).unwrap(), true));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_mul(u2::try_from(3_u8).unwrap()), (u2::try_from(1_u8).unwrap(), true));
        // not overflow
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_mul(u2::try_from(0_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_mul(u2::try_from(1_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_mul(u2::try_from(2_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(0_u8).unwrap().overflowing_mul(u2::try_from(3_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_mul(u2::try_from(0_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_mul(u2::try_from(1_u8).unwrap()), (u2::try_from(1_u8).unwrap(), false));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_mul(u2::try_from(2_u8).unwrap()), (u2::try_from(2_u8).unwrap(), false));
        assert_eq!(u2::try_from(1_u8).unwrap().overflowing_mul(u2::try_from(3_u8).unwrap()), (u2::try_from(3_u8).unwrap(), false));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_mul(u2::try_from(0_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(2_u8).unwrap().overflowing_mul(u2::try_from(1_u8).unwrap()), (u2::try_from(2_u8).unwrap(), false));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_mul(u2::try_from(0_u8).unwrap()), (u2::try_from(0_u8).unwrap(), false));
        assert_eq!(u2::try_from(3_u8).unwrap().overflowing_mul(u2::try_from(1_u8).unwrap()), (u2::try_from(3_u8).unwrap(), false));
    }

    #[test]
    fn test_unsigned_wrapping_mul() {
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_mul(u2::try_from(2_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_mul(u2::try_from(3_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_mul(u2::try_from(2_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_mul(u2::try_from(3_u8).unwrap()), u2::try_from(1_u8).unwrap());
        // not overflow
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_mul(u2::try_from(0_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_mul(u2::try_from(1_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_mul(u2::try_from(2_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap().wrapping_mul(u2::try_from(3_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_mul(u2::try_from(0_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_mul(u2::try_from(1_u8).unwrap()), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_mul(u2::try_from(2_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap().wrapping_mul(u2::try_from(3_u8).unwrap()), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_mul(u2::try_from(0_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap().wrapping_mul(u2::try_from(1_u8).unwrap()), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_mul(u2::try_from(0_u8).unwrap()), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap().wrapping_mul(u2::try_from(1_u8).unwrap()), u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_mul() {
        assert_eq!(u2::try_from(0_u8).unwrap() * u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() * u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() * u2::try_from(2_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() * u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() * u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() * u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() * u2::try_from(2_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() * u2::try_from(3_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() * u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() * u2::try_from(1_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() * u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() * u2::try_from(1_u8).unwrap(), u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_div_by_zero() {
        assert_panic!(u2::try_from(0_u8).unwrap() / u2::try_from(0_u8).unwrap());
        assert_panic!(u2::try_from(0_u8).unwrap() / u2::try_from(0_u8).unwrap());
        assert_panic!(u2::try_from(1_u8).unwrap() / u2::try_from(0_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() / u2::try_from(0_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() / u2::try_from(0_u8).unwrap());
    }

    #[test]
    fn test_unsigned_div() {
        assert_eq!(u2::try_from(0_u8).unwrap() / u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() / u2::try_from(2_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() / u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() / u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() / u2::try_from(2_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() / u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() / u2::try_from(1_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() / u2::try_from(2_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() / u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() / u2::try_from(1_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() / u2::try_from(2_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() / u2::try_from(3_u8).unwrap(), u2::try_from(1_u8).unwrap());
    }

    #[test]
    fn test_unsigned_rem_by_zero() {
        assert_panic!(u2::try_from(0_u8).unwrap() % u2::try_from(0_u8).unwrap());
        assert_panic!(u2::try_from(0_u8).unwrap() % u2::try_from(0_u8).unwrap());
        assert_panic!(u2::try_from(1_u8).unwrap() % u2::try_from(0_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() % u2::try_from(0_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() % u2::try_from(0_u8).unwrap());
    }

    #[test]
    fn test_unsigned_rem() {
        assert_eq!(u2::try_from(0_u8).unwrap() % u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() % u2::try_from(2_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() % u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() % u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() % u2::try_from(2_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() % u2::try_from(3_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() % u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() % u2::try_from(2_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() % u2::try_from(3_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() % u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() % u2::try_from(2_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() % u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
    }

    #[test]
    fn test_unsigned_bitand() {
        assert_eq!(u2::try_from(0_u8).unwrap() & u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() & u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() & u2::try_from(2_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() & u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() & u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() & u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() & u2::try_from(2_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() & u2::try_from(3_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() & u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() & u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() & u2::try_from(2_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() & u2::try_from(3_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() & u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() & u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() & u2::try_from(2_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() & u2::try_from(3_u8).unwrap(), u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_bitor() {
        assert_eq!(u2::try_from(0_u8).unwrap() | u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() | u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() | u2::try_from(2_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() | u2::try_from(3_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() | u2::try_from(0_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() | u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() | u2::try_from(2_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() | u2::try_from(3_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() | u2::try_from(0_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() | u2::try_from(1_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() | u2::try_from(2_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() | u2::try_from(3_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() | u2::try_from(0_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() | u2::try_from(1_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() | u2::try_from(2_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() | u2::try_from(3_u8).unwrap(), u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_bitxor() {
        assert_eq!(u2::try_from(0_u8).unwrap() ^ u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() ^ u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() ^ u2::try_from(2_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() ^ u2::try_from(3_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() ^ u2::try_from(0_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() ^ u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() ^ u2::try_from(2_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() ^ u2::try_from(3_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() ^ u2::try_from(0_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() ^ u2::try_from(1_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() ^ u2::try_from(2_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() ^ u2::try_from(3_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() ^ u2::try_from(0_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() ^ u2::try_from(1_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() ^ u2::try_from(2_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() ^ u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
    }

    #[test]
    fn test_unsigned_bitnot() {
        assert_eq!(!u2::try_from(0_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(!u2::try_from(1_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(!u2::try_from(2_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(!u2::try_from(3_u8).unwrap(), u2::try_from(0_u8).unwrap());
    }

    #[test]
    fn test_unsigned_shl_overflow() {
        assert_panic!(u2::try_from(0_u8).unwrap() << u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(0_u8).unwrap() << u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(1_u8).unwrap() << u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(1_u8).unwrap() << u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() << u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() << u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() << u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() << u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_shl() {
        assert_eq!(u2::try_from(0_u8).unwrap() << u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() << u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() << u2::try_from(0_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() << u2::try_from(1_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() << u2::try_from(0_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() << u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() << u2::try_from(0_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() << u2::try_from(1_u8).unwrap(), u2::try_from(2_u8).unwrap());
    }

    #[test]
    fn test_unsigned_shr_overflow() {
        assert_panic!(u2::try_from(0_u8).unwrap() >> u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(0_u8).unwrap() >> u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(1_u8).unwrap() >> u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(1_u8).unwrap() >> u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() >> u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(2_u8).unwrap() >> u2::try_from(3_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() >> u2::try_from(2_u8).unwrap());
        assert_panic!(u2::try_from(3_u8).unwrap() >> u2::try_from(3_u8).unwrap());
    }

    #[test]
    fn test_unsigned_shr() {
        assert_eq!(u2::try_from(0_u8).unwrap() >> u2::try_from(0_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(0_u8).unwrap() >> u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() >> u2::try_from(0_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(1_u8).unwrap() >> u2::try_from(1_u8).unwrap(), u2::try_from(0_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() >> u2::try_from(0_u8).unwrap(), u2::try_from(2_u8).unwrap());
        assert_eq!(u2::try_from(2_u8).unwrap() >> u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() >> u2::try_from(0_u8).unwrap(), u2::try_from(3_u8).unwrap());
        assert_eq!(u2::try_from(3_u8).unwrap() >> u2::try_from(1_u8).unwrap(), u2::try_from(1_u8).unwrap());
    }

    #[test]
    fn test_unsigned_bins() {
        assert_eq!(u2::try_from(0_u8).unwrap().to_str_radix(2), "00");
        assert_eq!(u2::try_from(1_u8).unwrap().to_str_radix(2), "01");
        assert_eq!(u2::try_from(2_u8).unwrap().to_str_radix(2), "10");
        assert_eq!(u2::try_from(3_u8).unwrap().to_str_radix(2), "11");
    }

    #[test]
    fn test_unsigned_leading_zeros() {
        assert_eq!(u2::try_from(0_u8).unwrap().leading_zeros(), 2);
        assert_eq!(u2::try_from(1_u8).unwrap().leading_zeros(), 1);
        assert_eq!(u2::try_from(2_u8).unwrap().leading_zeros(), 0);
        assert_eq!(u2::try_from(3_u8).unwrap().leading_zeros(), 0);
    }

    #[test]
    fn test_unsigned_trailing_zeros() {
        assert_eq!(u2::try_from(0_u8).unwrap().trailing_zeros(), 2);
        assert_eq!(u2::try_from(1_u8).unwrap().trailing_zeros(), 0);
        assert_eq!(u2::try_from(2_u8).unwrap().trailing_zeros(), 1);
        assert_eq!(u2::try_from(3_u8).unwrap().trailing_zeros(), 0);
    }

    #[test]
    fn test_unsigned_bit_len() {
        assert_eq!(u2::try_from(0_u8).unwrap().bit_len(), 0);
        assert_eq!(u2::try_from(1_u8).unwrap().bit_len(), 1);
        assert_eq!(u2::try_from(2_u8).unwrap().bit_len(), 2);
        assert_eq!(u2::try_from(3_u8).unwrap().bit_len(), 2);
    }
}
