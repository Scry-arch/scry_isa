use crate::Alu2OutputVariant;
use std::{
	convert::{TryFrom, TryInto},
	ops::{BitAnd, BitXor},
};

/// Trait for bits representing an integer value.
pub trait BitValue: TryFrom<i32, Error = ()>
{
	/// The number of bits needed to represent this value
	const SIZE: u32;

	/// Whether this value is a signed integer
	const SIGNED: bool;
	fn value(&self) -> i32;

	/// The highest integer value.
	fn get_max() -> Self;

	/// The lowest integer value.
	fn get_min() -> Self;

	/// Whether it is the highest value.
	fn is_max(&self) -> bool
	{
		self.value() == Self::get_max().value()
	}

	/// Whether it is the lowest value.
	fn is_min(&self) -> bool
	{
		self.value() == Self::get_min().value()
	}
}

/// Represents a set of N bits.
#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub struct Bits<const N: u32, const SIGNED: bool>
{
	pub value: i32,
}
impl<const N: u32, const SIGNED: bool> Bits<N, SIGNED>
{
	pub fn zero() -> Self
	{
		0.try_into().unwrap()
	}

	/// All bits set to 1.
	///
	/// For unsigned, equivalent to `get_max()`.
	pub fn saturated() -> Self
	{
		Self {
			value: if SIGNED { -1 } else { Self::get_max().value },
		}
	}

	/// All bits set to 0.
	pub fn cleared() -> Self
	{
		Self { value: 0 }
	}
}
impl<const N: u32, const SIGNED: bool> BitValue for Bits<N, SIGNED>
{
	const SIGNED: bool = SIGNED;
	const SIZE: u32 = N;

	fn value(&self) -> i32
	{
		self.value
	}

	fn get_max() -> Self
	{
		Self {
			value: if SIGNED { 2i32.pow(N) / 2 } else { 2i32.pow(N) } - 1,
		}
	}

	fn get_min() -> Self
	{
		Self {
			value: {
				if SIGNED
				{
					(2i32.pow(N) / 2) * -1
				}
				else
				{
					Self::cleared().value
				}
			},
		}
	}
}
impl<const N: u32, const SIGNED: bool> TryFrom<i32> for Bits<N, SIGNED>
{
	type Error = ();

	fn try_from(value: i32) -> Result<Self, Self::Error>
	{
		if Self::get_max().value() >= value && Self::get_min().value() <= value
		{
			Ok(Self { value })
		}
		else
		{
			Err(())
		}
	}
}
impl<const N: u32> From<Bits<N, false>> for Bits<N, true>
{
	fn from(x: Bits<N, false>) -> Self
	{
		// Reinterpret the bits as signed
		if x.value > Self::get_max().value
		{
			let remainder = x.value - Self::get_max().value - 1;
			(Self::get_min().value + remainder).try_into().unwrap()
		}
		else
		{
			x.value.try_into().unwrap()
		}
	}
}
impl<const N: u32> From<Bits<N, true>> for Bits<N, false>
{
	fn from(x: Bits<N, true>) -> Self
	{
		// Reinterpret the bits as signed
		if x.value < 0
		{
			let remainder = (-Bits::<N, true>::get_min().value) + x.value + 1;
			(Bits::<N, true>::get_max().value + remainder)
				.try_into()
				.unwrap()
		}
		else
		{
			(x.value).try_into().unwrap()
		}
	}
}

impl From<Bits<1, false>> for bool
{
	fn from(x: Bits<1, false>) -> Self
	{
		x.value == 1
	}
}
impl From<bool> for Bits<1, false>
{
	fn from(x: bool) -> Self
	{
		(x as i32).try_into().unwrap()
	}
}

impl From<Bits<3, false>> for Alu2OutputVariant
{
	fn from(x: Bits<3, false>) -> Self
	{
		use Alu2OutputVariant::*;
		match x.value
		{
			0b001 => High,
			0b010 => Low,
			0b011 => FirstLow,
			0b100 => FirstHigh,
			0b101 => NextHigh,
			0b110 => NextLow,
			_ => panic!("Invalid Alu2OutputVariant"),
		}
	}
}
impl From<Alu2OutputVariant> for Bits<3, false>
{
	fn from(x: Alu2OutputVariant) -> Self
	{
		use Alu2OutputVariant::*;
		(match x
		{
			High => 0b001,
			Low => 0b010,
			FirstLow => 0b011,
			FirstHigh => 0b100,
			NextHigh => 0b101,
			NextLow => 0b110,
		})
		.try_into()
		.unwrap()
	}
}

impl<
		const N: u32,
		const SIGNED: bool,
		const N1: u32,
		const SIGNED1: bool,
		const N2: u32,
		const SIGNED2: bool,
	> TryFrom<(Bits<N1, SIGNED1>, Bits<N2, SIGNED2>)> for Bits<N, SIGNED>
{
	type Error = ();

	fn try_from((high, low): (Bits<N1, SIGNED1>, Bits<N2, SIGNED2>)) -> Result<Self, Self::Error>
	{
		if N == (N1 + N2)
		{
			let mut result = high.value;
			result <<= N2;
			result += low.value;
			Ok(Self { value: result })
		}
		else
		{
			Err(())
		}
	}
}

impl<
		const N: u32,
		const SIGNED: bool,
		const N1: u32,
		const SIGNED1: bool,
		const N2: u32,
		const SIGNED2: bool,
	> TryFrom<Bits<N, SIGNED>> for (Bits<N1, SIGNED1>, Bits<N2, SIGNED2>)
{
	type Error = ();

	fn try_from(value: Bits<N, SIGNED>) -> Result<Self, Self::Error>
	{
		if N == (N1 + N2)
		{
			let low_value = value.value.bitand(Bits::<N2, false>::saturated().value);
			let mut high_value = value
				.value
				.bitand(Bits::<N2, false>::saturated().value.bitxor(-1))
				>> N2;
			if high_value >= Bits::<N1, SIGNED1>::get_max().value
			{
				// Must be negative
				high_value += Bits::<N1, false>::saturated().value.bitxor(-1);
			}
			Ok((Bits { value: high_value }, Bits { value: low_value }))
		}
		else
		{
			Err(())
		}
	}
}

/// Disallows a specific value from being accepted.
///
/// Otherwise, behaves like `B`.
#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub struct Exclude<B: BitValue, const EXCLUDED: i32>(B);
impl<B: BitValue, const EXCLUDED: i32> TryFrom<i32> for Exclude<B, EXCLUDED>
{
	type Error = ();

	fn try_from(value: i32) -> Result<Self, Self::Error>
	{
		if value != EXCLUDED
		{
			value.try_into().map(|v| Self(v))
		}
		else
		{
			Err(())
		}
	}
}
impl<B: BitValue, const EXCLUDED: i32> BitValue for Exclude<B, EXCLUDED>
{
	const SIGNED: bool = false;
	const SIZE: u32 = 0;

	fn value(&self) -> i32
	{
		self.0.value()
	}

	fn get_max() -> Self
	{
		let inner_max = B::get_max();
		let mut max = inner_max.value();

		let mut result = if EXCLUDED == inner_max.value()
		{
			Err(())
		}
		else
		{
			Ok(inner_max)
		};
		while let Err(_) = result
		{
			max -= 1;
			result = max.try_into();
		}
		result
			.map(|v| Self(v))
			.unwrap_or_else(|_| panic!("Couldn't find a max"))
	}

	fn get_min() -> Self
	{
		let inner_min = B::get_min();
		let mut min = inner_min.value();

		let mut result = if EXCLUDED == inner_min.value()
		{
			Err(())
		}
		else
		{
			Ok(inner_min)
		};
		while let Err(_) = result
		{
			min += 1;
			result = min.try_into();
		}
		result
			.map(|v| Self(v))
			.unwrap_or_else(|_| panic!("Couldn't find a max"))
	}
}
impl<const N: u32, const SIGNED: bool, const EXCLUDED: i32> From<Exclude<Bits<N, SIGNED>, EXCLUDED>>
	for Bits<N, SIGNED>
{
	fn from(value: Exclude<Bits<N, SIGNED>, EXCLUDED>) -> Self
	{
		value.0
	}
}
impl<const N: u32, const SIGNED: bool, const EXCLUDED: i32> From<Bits<N, SIGNED>>
	for Exclude<Bits<N, SIGNED>, EXCLUDED>
{
	fn from(value: Bits<N, SIGNED>) -> Self
	{
		value.value().try_into().unwrap()
	}
}

/// Like `Bits` except the signedness is not statically known
#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub struct BitsDyn<const N: u32>(bool, Bits<N, false>);
impl<const N: u32> BitsDyn<N>
{
	/// Whether the value is signed
	pub fn is_signed(&self) -> bool
	{
		self.0
	}
}
impl<const N: u32, const SIGNED: bool> From<Bits<N, SIGNED>> for BitsDyn<N>
{
	fn from(v: Bits<N, SIGNED>) -> Self
	{
		Self(
			SIGNED,
			if SIGNED
			{
				Bits::<N, true>::try_from(v.value()).unwrap().into()
			}
			else
			{
				Bits::<N, false>::try_from(v.value()).unwrap().into()
			},
		)
	}
}
impl<const N: u32> TryFrom<BitsDyn<N>> for Bits<N, true>
{
	type Error = ();

	fn try_from(value: BitsDyn<N>) -> Result<Self, Self::Error>
	{
		if value.0
		{
			Ok(value.1.into())
		}
		else
		{
			Err(())
		}
	}
}
impl<const N: u32> TryFrom<BitsDyn<N>> for Bits<N, false>
{
	type Error = ();

	fn try_from(value: BitsDyn<N>) -> Result<Self, Self::Error>
	{
		if !value.0
		{
			Ok(value.1.into())
		}
		else
		{
			Err(())
		}
	}
}
/// Reinterprets 9 bits as 1 flag bit (the most significant) for whether the
/// rest is signed.
/// Used for decoding the "const" instruction
impl From<Bits<9, false>> for BitsDyn<8>
{
	fn from(bits: Bits<9, false>) -> Self
	{
		let (signed, imm): (Bits<1, false>, Bits<8, false>) = bits.try_into().unwrap();
		if signed.value == 0
		{
			imm.into()
		}
		else
		{
			Bits::<8, true>::from(imm).into()
		}
	}
}
/// Reinterprets BitsDyn into Bits with 1 extra bit (the most significant)
/// as a flag for whether rest is signed.
/// Used for encoding the "const" instruction
impl From<BitsDyn<8>> for Bits<9, false>
{
	fn from(bits: BitsDyn<8>) -> Self
	{
		let sign_bits = Bits::<1, false>::try_from(bits.is_signed() as i32).unwrap();

		let imm_bits: Bits<8, false> = if bits.is_signed()
		{
			Bits::<8, true>::try_from(bits).unwrap().into()
		}
		else
		{
			Bits::<8, false>::try_from(bits).unwrap().into()
		};
		(sign_bits, imm_bits).try_into().unwrap()
	}
}
