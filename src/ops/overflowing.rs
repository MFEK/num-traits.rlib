use core::ops::{Add, Div, Mul, Shl, Shr, Sub};
#[cfg(has_i128)]
use core::{i128, u128};
use core::{i16, i32, i64, i8, isize};
use core::{u16, u32, u64, u8, usize};

macro_rules! overflowing_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: &Self) -> (Self, bool) {
                <$t>::$method(*self, *v)
            }
        }
    };
}

macro_rules! overflowing_u32_arg_impl {
    ($trait_name:ident, $method:ident, $t:ty) => {
        impl $trait_name for $t {
            #[inline]
            fn $method(&self, v: u32) -> (Self, bool) {
                <$t>::$method(*self, v)
            }
        }
    };
}

/// Performs addition with a flag for overflow.
pub trait OverflowingAdd: Sized + Add<Self, Output = Self> {
    /// Returns a tuple of the sum along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_add(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingAdd, overflowing_add, u8);
overflowing_impl!(OverflowingAdd, overflowing_add, u16);
overflowing_impl!(OverflowingAdd, overflowing_add, u32);
overflowing_impl!(OverflowingAdd, overflowing_add, u64);
overflowing_impl!(OverflowingAdd, overflowing_add, usize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingAdd, overflowing_add, u128);

overflowing_impl!(OverflowingAdd, overflowing_add, i8);
overflowing_impl!(OverflowingAdd, overflowing_add, i16);
overflowing_impl!(OverflowingAdd, overflowing_add, i32);
overflowing_impl!(OverflowingAdd, overflowing_add, i64);
overflowing_impl!(OverflowingAdd, overflowing_add, isize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingAdd, overflowing_add, i128);

/// Performs substraction with a flag for overflow.
pub trait OverflowingSub: Sized + Sub<Self, Output = Self> {
    /// Returns a tuple of the difference along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_sub(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingSub, overflowing_sub, u8);
overflowing_impl!(OverflowingSub, overflowing_sub, u16);
overflowing_impl!(OverflowingSub, overflowing_sub, u32);
overflowing_impl!(OverflowingSub, overflowing_sub, u64);
overflowing_impl!(OverflowingSub, overflowing_sub, usize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingSub, overflowing_sub, u128);

overflowing_impl!(OverflowingSub, overflowing_sub, i8);
overflowing_impl!(OverflowingSub, overflowing_sub, i16);
overflowing_impl!(OverflowingSub, overflowing_sub, i32);
overflowing_impl!(OverflowingSub, overflowing_sub, i64);
overflowing_impl!(OverflowingSub, overflowing_sub, isize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingSub, overflowing_sub, i128);

/// Performs multiplication with a flag for overflow.
pub trait OverflowingMul: Sized + Mul<Self, Output = Self> {
    /// Returns a tuple of the product along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    fn overflowing_mul(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingMul, overflowing_mul, u8);
overflowing_impl!(OverflowingMul, overflowing_mul, u16);
overflowing_impl!(OverflowingMul, overflowing_mul, u32);
overflowing_impl!(OverflowingMul, overflowing_mul, u64);
overflowing_impl!(OverflowingMul, overflowing_mul, usize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingMul, overflowing_mul, u128);

overflowing_impl!(OverflowingMul, overflowing_mul, i8);
overflowing_impl!(OverflowingMul, overflowing_mul, i16);
overflowing_impl!(OverflowingMul, overflowing_mul, i32);
overflowing_impl!(OverflowingMul, overflowing_mul, i64);
overflowing_impl!(OverflowingMul, overflowing_mul, isize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingMul, overflowing_mul, i128);

/// Performs division with a flag for overflow.
pub trait OverflowingDiv: Sized + Div<Self, Output = Self> {
    /// Calculates the divisor when self is divided by rhs.
    /// Returns a tuple of the divisor along with a boolean indicating whether an arithmetic overflow would occur.
    fn overflowing_div(&self, v: &Self) -> (Self, bool);
}

overflowing_impl!(OverflowingDiv, overflowing_div, u8);
overflowing_impl!(OverflowingDiv, overflowing_div, u16);
overflowing_impl!(OverflowingDiv, overflowing_div, u32);
overflowing_impl!(OverflowingDiv, overflowing_div, u64);
overflowing_impl!(OverflowingDiv, overflowing_div, usize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingDiv, overflowing_div, u128);

overflowing_impl!(OverflowingDiv, overflowing_div, i8);
overflowing_impl!(OverflowingDiv, overflowing_div, i16);
overflowing_impl!(OverflowingDiv, overflowing_div, i32);
overflowing_impl!(OverflowingDiv, overflowing_div, i64);
overflowing_impl!(OverflowingDiv, overflowing_div, isize);
#[cfg(has_i128)]
overflowing_impl!(OverflowingDiv, overflowing_div, i128);

pub trait OverflowingShl: Sized + Shl<Self, Output = Self> {
    /// Shifts self left by rhs bits.
    fn overflowing_shl(&self, rhs: u32) -> (Self, bool);
}

overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, u8);
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, u16);
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, u32);
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, u64);
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, usize);
#[cfg(has_i128)]
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, u128);

overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, i8);
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, i16);
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, i32);
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, i64);
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, isize);
#[cfg(has_i128)]
overflowing_u32_arg_impl!(OverflowingShl, overflowing_shl, i128);

#[test]
fn test_overflowing_traits() {
    fn overflowing_add<T: OverflowingAdd>(a: T, b: T) -> (T, bool) {
        a.overflowing_add(&b)
    }
    fn overflowing_sub<T: OverflowingSub>(a: T, b: T) -> (T, bool) {
        a.overflowing_sub(&b)
    }
    fn overflowing_mul<T: OverflowingMul>(a: T, b: T) -> (T, bool) {
        a.overflowing_mul(&b)
    }
    fn overflowing_div<T: OverflowingDiv>(a: T, b: T) -> (T, bool) {
        a.overflowing_div(&b)
    }
    fn overflowing_shl<T: OverflowingShl>(a: T, b: u32) -> (T, bool) {
        a.overflowing_shl(b)
    }
    assert_eq!(overflowing_add(5i16, 2), (7, false));
    assert_eq!(overflowing_add(i16::MAX, 1), (i16::MIN, true));
    assert_eq!(overflowing_sub(5i16, 2), (3, false));
    assert_eq!(overflowing_sub(i16::MIN, 1), (i16::MAX, true));
    assert_eq!(overflowing_mul(5i16, 2), (10, false));
    assert_eq!(overflowing_mul(1_000_000_000i32, 10), (1410065408, true));
    assert_eq!(overflowing_div(4, 2), (2, false));
    assert_eq!(overflowing_div(i16::MIN, -1), (i16::MIN, true));

    assert_eq!(overflowing_shl(0x4000u16, 1), (0x8000, false));
    assert_eq!(overflowing_shl(0x4000u16, 17), (0x8000, true));
}
