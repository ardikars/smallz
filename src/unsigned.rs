use alloc::fmt;
use alloc::format;
use alloc::string::String;
use core::cmp::Ordering;
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

            pub fn min(self, rhs: $name) -> $name {
                match self.0.cmp(&rhs.0) {
                    Ordering::Less => self,
                    Ordering::Greater => rhs,
                    Ordering::Equal => self,
                }
            }

            pub fn max(self, rhs: $name) -> $name {
                match self.0.cmp(&rhs.0) {
                    Ordering::Less => rhs,
                    Ordering::Greater => self,
                    Ordering::Equal => self,
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

        impl From<bool> for $name {
            fn from(value: bool) -> $name {
                $name(value as u8)
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

        impl TryFrom<usize> for $name {
            type Error = String;
            fn try_from(value: usize) -> Result<Self, Self::Error> {
                if value > Self::MAX.0 as usize {
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
                    panic!("attempt to {} with overflow", stringify!($method_assign));
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
                    <$type>::try_from((self.0 $op rhs.0) & Self::MASK).unwrap()
                } else {
                    panic!("attempt to shift {} by `{}`, which would overflow", stringify!($op), rhs.0)
                }
            }
        }

        impl $trait_assign for $type {
            fn $method_assign(&mut self, rhs: $type) {
                if u32::from(rhs.0) < Self::BITS {
                    self.0 = (self.0 $op rhs.0) & Self::MASK;
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
                <$type>::try_from((!self.0) & Self::MASK).unwrap()
            }
        }
    };
}

macro_rules! unsigned_overflowing_op {
    ($type:ty, $method:ident, $op:tt) => {
        pub fn $method(&self, rhs: $type) -> ($type, bool) {
            let r = self.0 $op rhs.0;
            if r > Self::MASK {
                (<$type>::try_from(r & Self::MASK).unwrap(), true)
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
            <$type>::try_from((self.0 $op rhs.0) & Self::MASK).unwrap()
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

pub(super) const U2_MIN_AS_U4: u4 = u4::ZERO;
pub(super) const U2_MAX_AS_U4: u4 = u4(3);
pub(super) const U2_BITS_AS_U4: u4 = u4(2);

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    macro_rules! assert_panic {
        ($expr:expr) => {
            assert!(
                catch_unwind(AssertUnwindSafe(|| $expr)).is_err(),
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
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_panic!(one + three);
        assert_panic!(two + two);
        assert_panic!(two + three);
        assert_panic!(three + one);
        assert_panic!(three + two);
        assert_panic!(three + three);

        let mut one = u2::try_from(1_u8).unwrap();
        let mut two = u2::try_from(2_u8).unwrap();
        let mut three = u2::try_from(3_u8).unwrap();
        assert_panic!(one += three);
        assert_panic!(two += two);
        assert_panic!(two += three);
        assert_panic!(three += one);
        assert_panic!(three += two);
        assert_panic!(three += three);
    }

    #[test]
    fn test_unsigned_overflowing_add() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(one.overflowing_add(three), (zero, true));
        assert_eq!(two.overflowing_add(two), (zero, true));
        assert_eq!(two.overflowing_add(three), (one, true));
        assert_eq!(three.overflowing_add(one), (zero, true));
        assert_eq!(three.overflowing_add(two), (one, true));
        assert_eq!(three.overflowing_add(three), (two, true));
        // not overflow
        assert_eq!(zero.overflowing_add(zero), (zero, false));
        assert_eq!(zero.overflowing_add(one), (one, false));
        assert_eq!(zero.overflowing_add(two), (two, false));
        assert_eq!(zero.overflowing_add(three), (three, false));
        assert_eq!(one.overflowing_add(zero), (one, false));
        assert_eq!(one.overflowing_add(one), (two, false));
        assert_eq!(one.overflowing_add(two), (three, false));
        assert_eq!(two.overflowing_add(zero), (two, false));
        assert_eq!(two.overflowing_add(one), (three, false));
        assert_eq!(three.overflowing_add(zero), (three, false));
    }

    #[test]
    fn test_unsigned_wrapping_add() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(one.wrapping_add(three), zero);
        assert_eq!(two.wrapping_add(two), zero);
        assert_eq!(two.wrapping_add(three), one);
        assert_eq!(three.wrapping_add(one), zero);
        assert_eq!(three.wrapping_add(two), one);
        assert_eq!(three.wrapping_add(three), two);
        // not overflow
        assert_eq!(zero.wrapping_add(zero), zero);
        assert_eq!(zero.wrapping_add(one), one);
        assert_eq!(zero.wrapping_add(two), two);
        assert_eq!(zero.wrapping_add(three), three);
        assert_eq!(one.wrapping_add(zero), one);
        assert_eq!(one.wrapping_add(one), two);
        assert_eq!(one.wrapping_add(two), three);
        assert_eq!(two.wrapping_add(zero), two);
        assert_eq!(two.wrapping_add(one), three);
        assert_eq!(three.wrapping_add(zero), three);
    }

    #[test]
    fn test_unsigned_add() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero + zero, zero);
        assert_eq!(zero + one, one);
        assert_eq!(zero + two, two);
        assert_eq!(zero + three, three);
        assert_eq!(one + zero, one);
        assert_eq!(one + one, two);
        assert_eq!(one + two, three);
        assert_eq!(two + zero, two);
        assert_eq!(two + one, three);
        assert_eq!(three + zero, three);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut += zero;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut += one;
        assert_eq!(zero_mut, one);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut += two;
        assert_eq!(zero_mut, two);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut += three;
        assert_eq!(zero_mut, three);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut += zero;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut += one;
        assert_eq!(one_mut, two);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut += two;
        assert_eq!(one_mut, three);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut += zero;
        assert_eq!(two_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut += one;
        assert_eq!(two_mut, three);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut += zero;
        assert_eq!(three_mut, three);
    }

    #[test]
    fn test_unsigned_sub_overflow() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_panic!(zero - one);
        assert_panic!(zero - two);
        assert_panic!(zero - three);
        assert_panic!(one - two);
        assert_panic!(one - three);
        assert_panic!(two - three);

        let mut zero = u2::try_from(0_u8).unwrap();
        let mut one = u2::try_from(1_u8).unwrap();
        let mut two = u2::try_from(2_u8).unwrap();
        assert_panic!(zero -= one);
        assert_panic!(zero -= two);
        assert_panic!(zero -= three);
        assert_panic!(one -= two);
        assert_panic!(one -= three);
        assert_panic!(two -= three);
    }

    #[test]
    fn test_unsigned_overflowing_sub() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero.overflowing_sub(one), (three, true));
        assert_eq!(zero.overflowing_sub(two), (two, true));
        assert_eq!(zero.overflowing_sub(three), (one, true));
        assert_eq!(one.overflowing_sub(two), (three, true));
        assert_eq!(one.overflowing_sub(three), (two, true));
        assert_eq!(two.overflowing_sub(three), (three, true));
        // not overflow
        assert_eq!(zero.overflowing_sub(zero), (zero, false));
        assert_eq!(one.overflowing_sub(zero), (one, false));
        assert_eq!(one.overflowing_sub(one), (zero, false));
        assert_eq!(two.overflowing_sub(zero), (two, false));
        assert_eq!(two.overflowing_sub(one), (one, false));
        assert_eq!(two.overflowing_sub(two), (zero, false));
        assert_eq!(three.overflowing_sub(zero), (three, false));
        assert_eq!(three.overflowing_sub(one), (two, false));
        assert_eq!(three.overflowing_sub(two), (one, false));
        assert_eq!(three.overflowing_sub(three), (zero, false));
    }

    #[test]
    fn test_unsigned_wrapping_sub() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero.wrapping_sub(one), three);
        assert_eq!(zero.wrapping_sub(two), two);
        assert_eq!(zero.wrapping_sub(three), one);
        assert_eq!(one.wrapping_sub(two), three);
        assert_eq!(one.wrapping_sub(three), two);
        assert_eq!(two.wrapping_sub(three), three);
        // not overflow
        assert_eq!(zero.wrapping_sub(zero), zero);
        assert_eq!(one.wrapping_sub(zero), one);
        assert_eq!(one.wrapping_sub(one), zero);
        assert_eq!(two.wrapping_sub(zero), two);
        assert_eq!(two.wrapping_sub(one), one);
        assert_eq!(two.wrapping_sub(two), zero);
        assert_eq!(three.wrapping_sub(zero), three);
        assert_eq!(three.wrapping_sub(one), two);
        assert_eq!(three.wrapping_sub(two), one);
        assert_eq!(three.wrapping_sub(three), zero);
    }

    #[test]
    fn test_unsigned_sub() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero - zero, zero);
        assert_eq!(one - zero, one);
        assert_eq!(one - one, zero);
        assert_eq!(two - zero, two);
        assert_eq!(two - one, one);
        assert_eq!(two - two, zero);
        assert_eq!(three - zero, three);
        assert_eq!(three - one, two);
        assert_eq!(three - two, one);
        assert_eq!(three - three, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut -= zero;
        assert_eq!(zero_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut -= zero;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut -= one;
        assert_eq!(one_mut, zero);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut -= zero;
        assert_eq!(two_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut -= one;
        assert_eq!(two_mut, one);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut -= two;
        assert_eq!(two_mut, zero);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut -= zero;
        assert_eq!(three_mut, three);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut -= one;
        assert_eq!(three_mut, two);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut -= two;
        assert_eq!(three_mut, one);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut -= three;
        assert_eq!(three_mut, zero);
    }

    #[test]
    fn test_unsigned_mul_overflow() {
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_panic!(two * two);
        assert_panic!(two * three);
        assert_panic!(three * two);
        assert_panic!(three * three);

        let mut two = u2::try_from(2_u8).unwrap();
        let mut three = u2::try_from(3_u8).unwrap();
        assert_panic!(two *= two);
        assert_panic!(two *= three);
        assert_panic!(three *= two);
        assert_panic!(three *= three);
    }

    #[test]
    fn test_unsigned_overflowing_mul() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(two.overflowing_mul(two), (zero, true));
        assert_eq!(two.overflowing_mul(three), (two, true));
        assert_eq!(three.overflowing_mul(two), (two, true));
        assert_eq!(three.overflowing_mul(three), (one, true));
        // not overflow
        assert_eq!(zero.overflowing_mul(zero), (zero, false));
        assert_eq!(zero.overflowing_mul(one), (zero, false));
        assert_eq!(zero.overflowing_mul(two), (zero, false));
        assert_eq!(zero.overflowing_mul(three), (zero, false));
        assert_eq!(one.overflowing_mul(zero), (zero, false));
        assert_eq!(one.overflowing_mul(one), (one, false));
        assert_eq!(one.overflowing_mul(two), (two, false));
        assert_eq!(one.overflowing_mul(three), (three, false));
        assert_eq!(two.overflowing_mul(zero), (zero, false));
        assert_eq!(two.overflowing_mul(one), (two, false));
        assert_eq!(three.overflowing_mul(zero), (zero, false));
        assert_eq!(three.overflowing_mul(one), (three, false));
    }

    #[test]
    fn test_unsigned_wrapping_mul() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(two.wrapping_mul(two), zero);
        assert_eq!(two.wrapping_mul(three), two);
        assert_eq!(three.wrapping_mul(two), two);
        assert_eq!(three.wrapping_mul(three), one);
        // not overflow
        assert_eq!(zero.wrapping_mul(zero), zero);
        assert_eq!(zero.wrapping_mul(one), zero);
        assert_eq!(zero.wrapping_mul(two), zero);
        assert_eq!(zero.wrapping_mul(three), zero);
        assert_eq!(one.wrapping_mul(zero), zero);
        assert_eq!(one.wrapping_mul(one), one);
        assert_eq!(one.wrapping_mul(two), two);
        assert_eq!(one.wrapping_mul(three), three);
        assert_eq!(two.wrapping_mul(zero), zero);
        assert_eq!(two.wrapping_mul(one), two);
        assert_eq!(three.wrapping_mul(zero), zero);
        assert_eq!(three.wrapping_mul(one), three);
    }

    #[test]
    fn test_unsigned_mul() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero * zero, zero);
        assert_eq!(zero * one, zero);
        assert_eq!(zero * two, zero);
        assert_eq!(zero * three, zero);
        assert_eq!(one * zero, zero);
        assert_eq!(one * one, one);
        assert_eq!(one * two, two);
        assert_eq!(one * three, three);
        assert_eq!(two * zero, zero);
        assert_eq!(two * one, two);
        assert_eq!(three * zero, zero);
        assert_eq!(three * one, three);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut *= zero;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut *= one;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut *= two;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut *= three;
        assert_eq!(zero_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut *= zero;
        assert_eq!(one_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut *= one;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut *= two;
        assert_eq!(one_mut, two);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut *= three;
        assert_eq!(one_mut, three);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut *= zero;
        assert_eq!(two_mut, zero);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut *= one;
        assert_eq!(two_mut, two);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut *= zero;
        assert_eq!(three_mut, zero);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut *= one;
        assert_eq!(three_mut, three);
    }

    #[test]
    fn test_unsigned_div_by_zero() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_panic!(zero / zero);
        assert_panic!(one / zero);
        assert_panic!(two / zero);
        assert_panic!(three / zero);

        let mut zero = u2::try_from(0_u8).unwrap();
        let mut one = u2::try_from(1_u8).unwrap();
        let mut two = u2::try_from(2_u8).unwrap();
        let mut three = u2::try_from(3_u8).unwrap();
        assert_panic!(zero /= zero);
        assert_panic!(one /= zero);
        assert_panic!(two /= zero);
        assert_panic!(three /= zero);
    }

    #[test]
    fn test_unsigned_div() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero / one, zero);
        assert_eq!(zero / two, zero);
        assert_eq!(zero / three, zero);
        assert_eq!(one / one, one);
        assert_eq!(one / two, zero);
        assert_eq!(one / three, zero);
        assert_eq!(two / one, two);
        assert_eq!(two / two, one);
        assert_eq!(two / three, zero);
        assert_eq!(three / one, three);
        assert_eq!(three / two, one);
        assert_eq!(three / three, one);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut /= one;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut /= two;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut /= three;
        assert_eq!(zero_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut /= one;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut /= two;
        assert_eq!(one_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut /= three;
        assert_eq!(one_mut, zero);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut /= one;
        assert_eq!(two_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut /= two;
        assert_eq!(two_mut, one);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut /= three;
        assert_eq!(two_mut, zero);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut /= one;
        assert_eq!(three_mut, three);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut /= two;
        assert_eq!(three_mut, one);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut /= three;
        assert_eq!(three_mut, one);
    }

    #[test]
    fn test_unsigned_rem_by_zero() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_panic!(zero % zero);
        assert_panic!(one % zero);
        assert_panic!(two % zero);
        assert_panic!(three % zero);

        let mut zero = u2::try_from(0_u8).unwrap();
        let mut one = u2::try_from(1_u8).unwrap();
        let mut two = u2::try_from(2_u8).unwrap();
        let mut three = u2::try_from(3_u8).unwrap();
        assert_panic!(zero %= zero);
        assert_panic!(one %= zero);
        assert_panic!(two %= zero);
        assert_panic!(three %= zero);
    }

    #[test]
    fn test_unsigned_rem() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero % one, zero);
        assert_eq!(zero % two, zero);
        assert_eq!(zero % three, zero);
        assert_eq!(one % one, zero);
        assert_eq!(one % two, one);
        assert_eq!(one % three, one);
        assert_eq!(two % one, zero);
        assert_eq!(two % two, zero);
        assert_eq!(two % three, two);
        assert_eq!(three % one, zero);
        assert_eq!(three % two, one);
        assert_eq!(three % three, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut %= one;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut %= two;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut %= three;
        assert_eq!(zero_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut %= one;
        assert_eq!(one_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut %= two;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut %= three;
        assert_eq!(one_mut, one);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut %= one;
        assert_eq!(two_mut, zero);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut %= two;
        assert_eq!(two_mut, zero);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut %= three;
        assert_eq!(two_mut, two);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut %= one;
        assert_eq!(three_mut, zero);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut %= two;
        assert_eq!(three_mut, one);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut %= three;
        assert_eq!(three_mut, zero);
    }

    #[test]
    fn test_unsigned_bitand() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero & zero, zero);
        assert_eq!(zero & one, zero);
        assert_eq!(zero & two, zero);
        assert_eq!(zero & three, zero);
        assert_eq!(one & zero, zero);
        assert_eq!(one & one, one);
        assert_eq!(one & two, zero);
        assert_eq!(one & three, one);
        assert_eq!(two & zero, zero);
        assert_eq!(two & one, zero);
        assert_eq!(two & two, two);
        assert_eq!(two & three, two);
        assert_eq!(three & zero, zero);
        assert_eq!(three & one, one);
        assert_eq!(three & two, two);
        assert_eq!(three & three, three);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut &= zero;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut &= one;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut &= two;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut &= three;
        assert_eq!(zero_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut &= zero;
        assert_eq!(one_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut &= one;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut &= two;
        assert_eq!(one_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut &= three;
        assert_eq!(one_mut, one);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut &= zero;
        assert_eq!(two_mut, zero);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut &= one;
        assert_eq!(two_mut, zero);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut &= two;
        assert_eq!(two_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut &= three;
        assert_eq!(two_mut, two);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut &= zero;
        assert_eq!(three_mut, zero);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut &= one;
        assert_eq!(three_mut, one);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut &= two;
        assert_eq!(three_mut, two);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut &= three;
        assert_eq!(three_mut, three);
    }

    #[test]
    fn test_unsigned_bitor() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero | zero, zero);
        assert_eq!(zero | one, one);
        assert_eq!(zero | two, two);
        assert_eq!(zero | three, three);
        assert_eq!(one | zero, one);
        assert_eq!(one | one, one);
        assert_eq!(one | two, three);
        assert_eq!(one | three, three);
        assert_eq!(two | zero, two);
        assert_eq!(two | one, three);
        assert_eq!(two | two, two);
        assert_eq!(two | three, three);
        assert_eq!(three | zero, three);
        assert_eq!(three | one, three);
        assert_eq!(three | two, three);
        assert_eq!(three | three, three);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut |= zero;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut |= one;
        assert_eq!(zero_mut, one);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut |= two;
        assert_eq!(zero_mut, two);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut |= three;
        assert_eq!(zero_mut, three);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut |= zero;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut |= one;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut |= two;
        assert_eq!(one_mut, three);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut |= three;
        assert_eq!(one_mut, three);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut |= zero;
        assert_eq!(two_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut |= one;
        assert_eq!(two_mut, three);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut |= two;
        assert_eq!(two_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut |= three;
        assert_eq!(two_mut, three);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut |= zero;
        assert_eq!(three, three);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut |= one;
        assert_eq!(three, three);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut |= two;
        assert_eq!(three, three);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut |= three;
        assert_eq!(three, three);
    }

    #[test]
    fn test_unsigned_bitxor() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero ^ zero, zero);
        assert_eq!(zero ^ one, one);
        assert_eq!(zero ^ two, two);
        assert_eq!(zero ^ three, three);
        assert_eq!(one ^ zero, one);
        assert_eq!(one ^ one, zero);
        assert_eq!(one ^ two, three);
        assert_eq!(one ^ three, two);
        assert_eq!(two ^ zero, two);
        assert_eq!(two ^ one, three);
        assert_eq!(two ^ two, zero);
        assert_eq!(two ^ three, one);
        assert_eq!(three ^ zero, three);
        assert_eq!(three ^ one, two);
        assert_eq!(three ^ two, one);
        assert_eq!(three ^ three, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut ^= zero;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut ^= one;
        assert_eq!(zero_mut, one);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut ^= two;
        assert_eq!(zero_mut, two);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut ^= three;
        assert_eq!(zero_mut, three);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut ^= zero;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut ^= one;
        assert_eq!(one_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut ^= two;
        assert_eq!(one_mut, three);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut ^= three;
        assert_eq!(one_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut ^= zero;
        assert_eq!(two_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut ^= one;
        assert_eq!(two_mut, three);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut ^= two;
        assert_eq!(two_mut, zero);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut ^= three;
        assert_eq!(two_mut, one);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut ^= zero;
        assert_eq!(three_mut, three);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut ^= one;
        assert_eq!(three_mut, two);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut ^= two;
        assert_eq!(three_mut, one);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut ^= three;
        assert_eq!(three_mut, zero);
    }

    #[test]
    fn test_unsigned_bitnot() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(!zero, three);
        assert_eq!(!one, two);
        assert_eq!(!two, one);
        assert_eq!(!three, zero);
    }

    #[test]
    fn test_unsigned_shl_overflow() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_panic!(zero << two);
        assert_panic!(zero << three);
        assert_panic!(one << two);
        assert_panic!(one << three);
        assert_panic!(two << two);
        assert_panic!(two << three);
        assert_panic!(three << two);
        assert_panic!(three << three);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        assert_panic!(zero_mut <<= two);
        let mut zero_mut = u2::try_from(0_u8).unwrap();
        assert_panic!(zero_mut <<= three);
        let mut one_mut = u2::try_from(1_u8).unwrap();
        assert_panic!(one_mut <<= two);
        let mut one_mut = u2::try_from(1_u8).unwrap();
        assert_panic!(one_mut <<= three);
        let mut two_mut = u2::try_from(2_u8).unwrap();
        assert_panic!(two_mut <<= two);
        let mut two_mut = u2::try_from(2_u8).unwrap();
        assert_panic!(two_mut <<= three);
        let mut three_mut = u2::try_from(3_u8).unwrap();
        assert_panic!(three_mut <<= two);
        let mut three_mut = u2::try_from(3_u8).unwrap();
        assert_panic!(three_mut <<= three);
    }

    #[test]
    fn test_unsigned_shl() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero << zero, zero);
        assert_eq!(zero << one, zero);
        assert_eq!(one << zero, one);
        assert_eq!(one << one, two);
        assert_eq!(two << zero, two);
        assert_eq!(two << one, zero);
        assert_eq!(three << zero, three);
        assert_eq!(three << one, two);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut <<= zero;
        assert_eq!(zero_mut, zero);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut <<= one;
        assert_eq!(zero_mut, zero);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut <<= zero;
        assert_eq!(one_mut, one);

        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut <<= one;
        assert_eq!(one_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut <<= zero;
        assert_eq!(two_mut, two);

        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut <<= one;
        assert_eq!(two_mut, zero);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut <<= zero;
        assert_eq!(three_mut, three);

        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut <<= one;
        assert_eq!(three_mut, two);
    }

    #[test]
    fn test_unsigned_shr_overflow() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_panic!(zero >> two);
        assert_panic!(zero >> three);
        assert_panic!(one >> two);
        assert_panic!(one >> three);
        assert_panic!(two >> two);
        assert_panic!(two >> three);
        assert_panic!(three >> two);
        assert_panic!(three >> three);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        assert_panic!(zero_mut >>= two);
        let mut zero_mut = u2::try_from(0_u8).unwrap();
        assert_panic!(zero_mut >>= three);
        let mut one_mut = u2::try_from(1_u8).unwrap();
        assert_panic!(one_mut >>= two);
        let mut one_mut = u2::try_from(1_u8).unwrap();
        assert_panic!(one_mut >>= three);
        let mut two_mut = u2::try_from(2_u8).unwrap();
        assert_panic!(two_mut >>= two);
        let mut two_mut = u2::try_from(2_u8).unwrap();
        assert_panic!(two_mut >>= three);
        let mut three_mut = u2::try_from(3_u8).unwrap();
        assert_panic!(three_mut >>= two);
        let mut three_mut = u2::try_from(3_u8).unwrap();
        assert_panic!(three_mut >>= three);
    }

    #[test]
    fn test_unsigned_shr() {
        let zero = u2::try_from(0_u8).unwrap();
        let one = u2::try_from(1_u8).unwrap();
        let two = u2::try_from(2_u8).unwrap();
        let three = u2::try_from(3_u8).unwrap();
        assert_eq!(zero >> zero, zero);
        assert_eq!(zero >> one, zero);
        assert_eq!(one >> zero, one);
        assert_eq!(one >> one, zero);
        assert_eq!(two >> zero, two);
        assert_eq!(two >> one, one);
        assert_eq!(three >> zero, three);
        assert_eq!(three >> one, one);

        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut >>= zero;
        assert_eq!(zero_mut, zero);
        let mut zero_mut = u2::try_from(0_u8).unwrap();
        zero_mut >>= one;
        assert_eq!(zero_mut, zero);
        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut >>= zero;
        assert_eq!(one_mut, one);
        let mut one_mut = u2::try_from(1_u8).unwrap();
        one_mut >>= one;
        assert_eq!(one_mut, zero);
        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut >>= zero;
        assert_eq!(two_mut, two);
        let mut two_mut = u2::try_from(2_u8).unwrap();
        two_mut >>= one;
        assert_eq!(two_mut, one);
        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut >>= zero;
        assert_eq!(three_mut, three);
        let mut three_mut = u2::try_from(3_u8).unwrap();
        three_mut >>= one;
        assert_eq!(three_mut, one);
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

    #[test]
    fn test_min_max() {
        assert_eq!(u2::from(false), u2::from(true).min(u2::from(false)));
        assert_eq!(u2::from(true), u2::from(true).min(u2::from(true)));
        assert_eq!(u2::from(false), u2::from(false).min(u2::from(true)));

        assert_eq!(u2::from(true), u2::from(true).max(u2::from(false)));
        assert_eq!(u2::from(true), u2::from(true).max(u2::from(true)));
        assert_eq!(u2::from(true), u2::from(false).max(u2::from(true)));
    }

    #[test]
    fn test_to_string_radix() {
        assert_eq!("f", u4::try_from(15_u8).unwrap().to_str_radix(16));
        assert_eq!("15", u4::try_from(15_u8).unwrap().to_str_radix(10));
        assert_eq!("17", u4::try_from(15_u8).unwrap().to_str_radix(8));
        assert_eq!("1111", u4::try_from(15_u8).unwrap().to_str_radix(2));
    }

    #[test]
    #[should_panic]
    fn test_to_string_unknown_radix() {
        let _ = u4::try_from(15_u8).unwrap().to_str_radix(15);
    }

    #[test]
    fn test_convert() {
        assert_eq!(0, u4::from(false).0);
        assert_eq!(1, u4::from(true).0);

        assert_eq!(15, u4::try_from(15_u8).unwrap().0);
        assert_eq!(
            "value 16 is out of range for u4",
            u4::try_from(16_u8).unwrap_err()
        );
        assert_eq!(15, u8::from(u4::MAX));

        assert_eq!(15, u4::try_from(15_u16).unwrap().0);
        assert_eq!(
            "value 16 is out of range for u4",
            u4::try_from(16_u16).unwrap_err()
        );
        assert_eq!(15, u16::from(u4::MAX));

        assert_eq!(15, u4::try_from(15_u32).unwrap().0);
        assert_eq!(
            "value 16 is out of range for u4",
            u4::try_from(16_u32).unwrap_err()
        );
        assert_eq!(15, u32::from(u4::MAX));

        assert_eq!(15, u4::try_from(15_u64).unwrap().0);
        assert_eq!(
            "value 16 is out of range for u4",
            u4::try_from(16_u64).unwrap_err()
        );
        assert_eq!(15, u64::from(u4::MAX));

        assert_eq!(15, u4::try_from(15_u128).unwrap().0);
        assert_eq!(
            "value 16 is out of range for u4",
            u4::try_from(16_u128).unwrap_err()
        );
        assert_eq!(15, u128::from(u4::MAX));

        assert_eq!(15, u4::try_from(15_usize).unwrap().0);
        assert_eq!(
            "value 16 is out of range for u4",
            u4::try_from(16_usize).unwrap_err()
        );
        assert_eq!(15, usize::from(u4::MAX));

        assert_eq!(u2::from(true), u2::try_from(u4::from(true)).unwrap());
        assert_eq!(
            "value 15 is out of range for u2",
            u2::try_from(u4::MAX).unwrap_err()
        );
        assert_eq!(u4::from(true), u4::from(u2::from(true)));
    }

    #[test]
    fn test_display() {
        println!("{}", u2::MIN);
    }
}
