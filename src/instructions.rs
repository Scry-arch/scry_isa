use crate::{Bits, BitsDyn};
use duplicate::duplicate;
use std::convert::TryInto;
use variant_count::VariantCount;

duplicate! {
	[
		name 					variants;
		[AluVariant]			[Inc, Dec, Add, Sub, ShiftLeft, ShiftRight, RotateLeft, RotateRight,
									Mul, BitAnd, BitOr];
		[Alu2Variant]			[Add, Sub, ShiftLeft, ShiftRight];
		[Alu2OutputVariant]		[High, Low, FirstLow, FirstHigh, NextHigh, NextLow];
		[CallVariant]			[Ret, Call]; //[, Portal, Ret, Trap]
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
	/// 0. Target whose outputs to capture
	/// 0. Target to get the captured inputs
	Capture(Bits<5, false>, Bits<5, false>),

	/// The duplicate instruction.
	///
	/// Fields:
	/// 0. Whether a third duplicate should be sent to the next instruction.
	/// 0. Output target 1.
	/// 0. Output target 2.
	Duplicate(bool, Bits<5, false>, Bits<5, false>),

	/// The echo instruction.
	///
	/// Fields:
	/// 0. Whether the remaining inputs should be output to the the next
	/// instruction.
	/// 0. Output target 1.
	/// 0. Output target 2.
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
	Load(bool, Bits<3, false>, Bits<5, false>),

	/// The store instruction.
	Store,

	/// The request instruction.
	Request(Bits<8, false>),

	/// The constant instruction.
	///
	/// Fields:
	/// 0. Whether the created constant is signed or not
	/// 0. The raw bits of the constant. If signed, should be handled
	/// accordingly.
	Constant(BitsDyn<8>),
}

impl Instruction
{
	/// Returns the canonical `nop` instruction.
	pub fn nop() -> Self
	{
		Self::Capture(0.try_into().unwrap(), 0.try_into().unwrap())
	}
}
