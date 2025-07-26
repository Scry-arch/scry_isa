use crate::Bits;
use duplicate::duplicate;
use std::convert::TryInto;
use variant_count::VariantCount;

duplicate! {
	[
		name 					variants;
		[AluVariant]			[Add, Sub, ShiftLeft, ShiftRight, RotateLeft, RotateRight, BitAnd, BitOr, Equal, LessThan, GreaterThan];
		[Alu2Variant]			[Add, Sub, Multiply];
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

/// Lists basic types.
///
/// Converting to/from Bits<SIZE, false> using TryFrom/TryInto is the only
/// correct way to encode/decode types.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Type
{
	/// Unsigned integer of the given power of 2. I.e., 0 is 1 byte, 1 is 2
	/// bytes, etc.
	Uint(u8),
	/// Signed integer of the given power of 2. I.e., 0 is 1 byte, 1 is 2 bytes,
	/// etc.
	Int(u8),
}
impl Type
{
	/// Returns the power of 2 size of this type.
	pub fn size_pow2(&self) -> u8
	{
		*match self
		{
			Type::Uint(x) if x < &4 => x,
			Type::Int(x) if x < &4 => x,
			_ => unreachable!("Invalid type size: {:?}", self),
		}
	}

	/// Returns the size of this type in bytes
	pub fn size(&self) -> usize
	{
		2u32.pow(self.size_pow2() as u32) as usize
	}

	pub fn is_signed_int(&self) -> bool
	{
		if let Type::Int(_) = self
		{
			true
		}
		else
		{
			false
		}
	}

	pub fn is_unsigned_int(&self) -> bool
	{
		if let Type::Uint(_) = self
		{
			true
		}
		else
		{
			false
		}
	}
}
impl<const SIZE: u32> TryFrom<Type> for Bits<SIZE, false>
{
	type Error = ();

	fn try_from(ty: Type) -> Result<Self, Self::Error>
	{
		match ty
		{
			Type::Uint(x) => ((x * 2) as i32).try_into(),
			Type::Int(x) => (((x * 2) + 1) as i32).try_into(),
		}
	}
}
impl<const SIZE: u32> TryFrom<Bits<SIZE, false>> for Type
{
	type Error = ();

	fn try_from(bits: Bits<SIZE, false>) -> Result<Self, Self::Error>
	{
		assert!(SIZE <= 8);
		let encoding = (bits.value / 2) as u8;
		Ok(
			if bits.value % 2 == 0
			{
				Type::Uint(encoding)
			}
			else
			{
				Type::Int(encoding)
			},
		)
	}
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
	/// 0. Operation
	/// 0. Output target
	Alu(AluVariant, Bits<5, false>),

	/// The double-output ALU instruction.
	///
	/// Fields:
	/// 0. Operation
	/// 0. Output type
	/// 0. Output target
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
	/// 0. Whether the load is stack-based or not. True is stack-based.
	/// 0. The type to be loaded.
	/// 0. Stack index to load from or output offset.
	Load(bool, Bits<4, false>, Bits<5, false>),

	/// The store instruction.
	Store,

	/// The stack store instruction.
	///
	/// 0. The index to store at
	StoreStack(Bits<5, false>),

	/// The stack address instruction.
	///
	/// 0. The scalar size of the object as a power of two. I.e. 0 is 1 byte, 1
	/// is 2 bytes, 2 is 4 bytes, etc.
	/// 0. Stack index to get the address of.
	StackAddr(Bits<2, false>, Bits<5, false>),

	/// The stack address instruction.
	///
	/// 0. Whether reserving or freeing the stack. `true`=reserving.
	/// 0. Power of 2 amount of bytes to reserve or free. I.e. 0 is 1 byte, 1
	/// is 2 bytes, 2 is 4 bytes, etc.
	/// 0. Whether targeting base or total stack frame
	StackRes(bool, Bits<4, false>, bool),

	/// No-operation instruction.
	NoOp,

	/// The request instruction.
	Request(Bits<8, false>),

	/// The constant instruction.
	///
	/// Fields:
	/// 0. Whether the created constant is signed or not
	/// 0. The raw bits of the constant. If signed, should be handled
	/// accordingly.
	Constant(Bits<3, false>, Bits<8, false>),
}
