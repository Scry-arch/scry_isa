use duplicate::{duplicate_inline};
use quickcheck::{Arbitrary, Gen};
use rand::Rng;
use std::convert::TryFrom;
use std::ops::{BitAnd, BitXor};

/// Represents a set of N bits.
#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub struct Bits<const N: u32, const SIGNED: bool> {
	value: i32
}

impl<const N: u32, const SIGNED: bool> Bits<N, SIGNED> {
	pub fn new(value: i32) -> Option<Self> {
		if Self::max().value() >= value &&
			Self::min().value() <= value {
			Some(Self{value: value})
		} else {
			None
		}
	}
	
	pub fn value(&self) -> i32 {
		self.value
	}
	
	pub fn saturated() -> Self {
		Self{value:
			if SIGNED {
				-1
			} else {
				Self::max().value
			}
		}
	}
	
	pub fn cleared() -> Self {
		Self{value: 0}
	}
	
	pub fn max() -> Self
	{
		Self{value:
			if SIGNED {
				2i32.pow(N)/2
			} else {
				2i32.pow(N)
			} - 1
		}
	}
	
	pub fn min() -> Self
	{
		Self{value: {
			if SIGNED {
				(2i32.pow(N)/2) * -1
			} else {
				Self::cleared().value
			}
		}}
	}
}

impl<
	const N: u32,
	const SIGNED: bool,
	const N1: u32,
	const SIGNED1: bool,
	const N2: u32,
	const SIGNED2: bool
> TryFrom<(Bits<N1,SIGNED1>, Bits<N2, SIGNED2>)>
	for Bits<N, SIGNED>
{
	type Error = ();
	
	fn try_from((high, low): (Bits<N1, SIGNED1>, Bits<N2, SIGNED2>)) -> Result<Self, Self::Error> {
		if N == (N1 + N2) {
			let mut result = high.value;
			result <<= N1;
			result += low.value;
			Ok(Self{value: result})
		} else {
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
	const SIGNED2: bool
> TryFrom<Bits<N, SIGNED>>
for (Bits<N1,SIGNED1>, Bits<N2, SIGNED2>)
{
	type Error = ();
	
	fn try_from(value: Bits<N, SIGNED>) -> Result<Self, Self::Error> {
		if N == (N1 + N2) {
			let low_value = value.value.bitand(Bits::<N2,false>::saturated().value);
			let mut high_value = value.value.bitand(
				Bits::<N2,false>::saturated().value.bitxor(-1)
			) >> N2;
			if high_value >= Bits::<N1,SIGNED1>::max().value {
				// Must be negative
				high_value += Bits::<N1,false>::saturated().value.bitxor(-1);
			}
			Ok((Bits{ value: high_value}, Bits{value: low_value}))
		} else {
			Err(())
		}
	}
}

impl<const N: u32, const SIGNED: bool> Arbitrary for Bits<N, SIGNED>
{
	fn arbitrary<G: Gen>(g: &mut G) -> Self {
		Bits{value: g.gen_range(Self::min().value, Self::max().value)}
	}
}

duplicate_inline! {
	[
		// variants; [Call, Portal, Ret, Trap];
		variants; [Ret];
	]
	/// Variants of the call instruction
	#[derive(Debug, Clone, Eq, PartialEq)]
	pub enum CallVariant {
		variants
	}
	
	impl Arbitrary for CallVariant
	{
		fn arbitrary<G: Gen>(g: &mut G) -> Self {
			use CallVariant::*;
			use rand::seq::SliceRandom;
			[variants].choose(g).unwrap().clone()
		}
	}
}

duplicate_inline! {
	[
		variants; [Reserve, Free];
	]
	#[derive(Debug, Clone, Eq, PartialEq)]
	pub enum StackControlVariant {
		variants
	}
	
	impl Arbitrary for StackControlVariant
	{
		fn arbitrary<G: Gen>(g: &mut G) -> Self {
			use StackControlVariant::*;
			use rand::seq::SliceRandom;
			[variants].choose(g).unwrap().clone()
		}
	}
}

/// All instructions
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Instruction {
	/// The jump instruction.
	///
	/// Fields:
	/// 0. The branch target offset.
	/// 0. The branch location offset.
	Jump(Bits<7,true>,Bits<6,false>),
	
	/// load instruction.
	///
	/// Fields
	/// 0. Whether the loaded value is signed.
	/// 0. The length of the loaded value.
	/// 0. The size of the loaded value.
	/// 0. Whether the primary address space is the target.
	/// 0. The "ar" flags.
	Load(bool, Bits<3,false>, Bits<3,false>,bool, Bits<2,false>),
	
	/// The echo instruction.
	///
	/// Fields:
	/// 0. Output target 1.
	/// 0. Output target 2.
	/// 0. Whether the remaining inputs should be output to the the next instruction.
	Echo(Bits<5,false>, Bits<5,false>, bool),
	
	/// The ALU instruction.
	///
	/// Fields:
	/// 0. Output target.
	/// 0. Function specifier.
	/// 0. Modifier.
	Alu(Bits<5,false>, Bits<4,false>, Bits<3,false>),
	
	/// The call instruction.
	///
	/// Fields:
	/// 0. The variant.
	/// 0. The branch location offset.
	Call(CallVariant, Bits<6,false>),
	
	// The stack control instruction.
	//
	// First field is the variant.
	// Second field is whether the primary stack is the target.
	//     If false, the secondary stack is the target.
	// Third field is the number of bytes to free/reserve
	// StackControl(StackControlVariant, bool, Bits<5>),
	
	// load from stack instruction.
	//
	// First is whether the loaded value is signed.
	// Second is the length of the loaded value.
	// Third is the size of the loaded value.
	// Fourth is the stack address offset.
	// LoadStack(bool, Bits<3>, Bits<3>, Bits<6>),
}

impl Arbitrary for Instruction
{
	fn arbitrary<G: Gen>(g: &mut G) -> Self {
		use Instruction::*;
		match g.gen_range(0, 3) {
			0 => Jump(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			1 => Call(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			2 => Echo(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			x => panic!("Unsupported: {}", x)
		}
	}
}