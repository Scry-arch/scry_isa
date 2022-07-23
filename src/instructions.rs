use duplicate::duplicate;
use std::{
	convert::{TryFrom, TryInto},
	ops::{BitAnd, BitXor},
};
use variant_count::VariantCount;

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
			result <<= N1;
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

duplicate! {
	[
		name 					variants;
		[AluVariant]			[Inc, Dec, Add, Sub, ShiftLeft, ShiftRight, RotateLeft, RotateRight];
		[Alu2Variant]			[Add, Sub, ShiftLeft, ShiftRight];
		[Alu2OutputVariant]		[High, Low, FirstLow, FirstHigh, NextHigh, NextLow];
		[CallVariant]			[Ret]; //[Call, Portal, Ret, Trap]
		[StackControlVariant] 	[Reserve, Free];
	]
	#[derive(Debug, Copy, Clone, Eq, PartialEq)]
	pub enum name {
		variants
	}
	impl name {
		pub const ALL_VARIANTS: &'static [Self] = {
			use name::*;
			&[variants]
		};
	}
}

#[derive(Debug, Clone, Eq, PartialEq, VariantCount)]
pub enum InstructionFormat
{
	/// The NEXT format (i.e. a single ouput to next instruction).
	/// The boolean is whether its the load-stack instruction.
	Next(bool),

	/// The NOON format (i.e. none or 1 output
	/// The bist are the offset of the output
	Noon(Bits<5, false>),

	/// the ALU format
	Alu,

	/// The DOUB format (two outputs with options
	Doub(Bits<5, false>, Bits<5, false>),
}

/// All instructions
#[derive(Debug, Clone, Eq, PartialEq, VariantCount)]
pub enum Instruction
{
	/// An invalid instruction.
	///
	/// Field 0 is the value of the instruction
	Invalid(u16),

	/// The jump instruction.
	///
	/// Fields:
	/// 0. The branch target offset.
	/// 0. The branch location offset.
	Jump(Bits<7, true>, Bits<6, false>),

	/// The capture instruction.
	///
	/// Fields:
	/// 0. Output target 1.
	/// 0. Output target 2.
	Capture(Bits<5, false>, Bits<5, false>),

	/// The duplicate instruction.
	///
	/// Fields:
	/// 0. Output target 1.
	/// 0. Output target 2.
	/// 0. Whether a third duplicate should be sent to the next instruction.
	Duplicate(bool, Bits<5, false>, Bits<5, false>),

	/// The echo instruction.
	///
	/// Fields:
	/// 0. Output target 1.
	/// 0. Output target 2.
	/// 0. Whether the remaining inputs should be output to the the next
	/// instruction.
	Echo(bool, Bits<5, false>, Bits<5, false>),

	/// The long echo instruction.
	///
	/// Fields:
	/// 0. Output target.
	EchoLong(Bits<10, false>),

	/// The single-output ALU instruction.
	///
	/// Fields:
	/// 0. Output target.
	Alu(AluVariant, Bits<5, false>),

	/// The single-output ALU instruction.
	///
	/// Fields:
	/// 0. Output target.
	Alu2(Alu2Variant, Alu2OutputVariant, Bits<5, false>),

	/// The call instruction.
	///
	/// Fields:
	/// 0. The variant.
	/// 0. The branch location offset.
	Call(CallVariant, Bits<6, false>),

	/// The pick instruction.
	///
	/// Fields:
	/// 0. Output target.
	Pick(Bits<5, false>),

	/// The pick-immediate instruction.
	///
	/// Fields:
	/// 0. Immediate value for the pick condition.
	/// 0. Output target.
	PickI(Bits<6, false>, Bits<5, false>),

	/// The integer load instruction.
	///
	/// Fields:
	/// 0. Whether the loaded integer is signed or unsigned. `true` is signed.
	/// 0. The scalar size to load as a power of two. I.e. 0 loads 1 byte, 1
	/// loads 2 bytes, 2 loads 4 bytes, etc.
	Load(bool, Bits<3, false>),

	/// The store instruction.
	Store,

	Nop,

	/// The request instruction.
	Request(Exclude<Bits<8, false>, 0>),
}
