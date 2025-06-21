use crate::{
	arbitrary::*, Alu2OutputVariant, Alu2Variant, AluVariant, CallVariant, Instruction,
	StackControlVariant, Type,
};
use duplicate::duplicate;
use quickcheck::{Arbitrary, Gen};
use std::{fmt::Debug, iter::once};

impl Arbitrary for Type
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		let signed = bool::arbitrary(g);
		let size = u8::arbitrary(g) % 4;

		if signed
		{
			Type::Int(size)
		}
		else
		{
			Type::Uint(size)
		}
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		Box::new(once(self.clone()))
	}
}

impl Arbitrary for Instruction
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		use Instruction::*;
		match gen_range(g, 0, Instruction::VARIANT_COUNT)
		{
			0 => Jump(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			1 => Call(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			2 =>
			{
				Echo(
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
				)
			},
			3 => EchoLong(Arbitrary::arbitrary(g)),
			4 => Alu(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			5 =>
			{
				Alu2(
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
				)
			},
			6 =>
			{
				Duplicate(
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
				)
			},
			7 => Capture(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			8 => Pick(Arbitrary::arbitrary(g)),
			9 => PickI(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			10 =>
			{
				Load(
					Arbitrary::arbitrary(g),
					Type::arbitrary(g).try_into().unwrap(),
					Arbitrary::arbitrary(g),
				)
			},
			11 => Store,
			12 => StoreStack(Arbitrary::arbitrary(g)),
			13 => NoOp,
			14 => Request(Arbitrary::arbitrary(g)),
			15 => Constant(Arbitrary::arbitrary(g)),
			16 => StackAddr(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			17 =>
			{
				StackRes(
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
				)
			},
			18 => Invalid(0),
			x => panic!("Missing arbitrary implement for instruction: {}", x),
		}
	}
}

duplicate! {
	[name;[AluVariant];[Alu2Variant];[Alu2OutputVariant];[CallVariant];[StackControlVariant];]
	impl Arbitrary for name
	{
		fn arbitrary(g: &mut Gen) -> Self {
			g.choose(&name::ALL_VARIANTS).unwrap().clone()
		}
	}
}

/// Trait for arbitrary-instruction-generating structs
pub trait ArbInstruction: Arbitrary + Debug
{
	fn extract(self) -> Instruction;
}
impl ArbInstruction for Instruction
{
	fn extract(self) -> Instruction
	{
		self
	}
}

/// Arbitrary instructions that output at least one value using an offset.
#[derive(Clone, Debug)]
pub struct WithOutput(pub Instruction);
impl ArbInstruction for WithOutput
{
	fn extract(self) -> Instruction
	{
		self.0
	}
}
impl Arbitrary for WithOutput
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		use Instruction::*;
		Self(match gen_range(g, 0, 9)
		{
			0 =>
			{
				Echo(
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
				)
			},
			1 => EchoLong(Arbitrary::arbitrary(g)),
			2 => Alu(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			3 =>
			{
				Alu2(
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
				)
			},
			4 =>
			{
				Duplicate(
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
					Arbitrary::arbitrary(g),
				)
			},
			5 => Capture(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			6 => Pick(Arbitrary::arbitrary(g)),
			7 => PickI(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			8 =>
			{
				Load(
					Arbitrary::arbitrary(g),
					Type::arbitrary(g).try_into().unwrap(),
					Arbitrary::arbitrary(g),
				)
			},
			_ => unreachable!(),
		})
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		Box::new(self.0.shrink().map(|i| Self(i)))
	}
}
