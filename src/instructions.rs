use crate::Bits;
use duplicate::duplicate;
use std::convert::TryInto;
use variant_count::VariantCount;

duplicate! {
	[
		name 					variants;
		[AluVariant]			[Add, Sub, BitAnd, BitOr, BitXor, Equal, LessThan, GreaterThan, IsNar, NarTo];
		[Alu2Variant]			[Add, Sub, Multiply, Shift, Division];
		[Alu2OutputVariant]		[HighOnly, LowOnly, LowFirst, HighFirst, HighNext, LowNext];
		[CallVariant]			[Ret, Call];
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
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
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
	PickI(Bits<2, false>, Bits<5, false>),

	/// The load instruction.
	///
	/// Fields:
	/// 0. The type to be loaded.
	/// 0. Output offset.
	Load(Bits<4, false>, Bits<5, false>),

	/// The stack load instruction.
	///
	/// Fields:
	/// 0. The type to be loaded.
	/// 0. The index to load from.
	LoadStack(Bits<4, false>, Bits<5, false>),

	/// The store instruction.
	Store,

	/// The stack store instruction.
	///
	/// 0. The index to store at.
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

	/// The constant instruction.
	///
	/// Fields:
	/// 0. Whether the created constant is signed or not
	/// 0. The raw bits of the constant. If signed, should be handled
	/// accordingly.
	Constant(Bits<3, false>, Bits<8, false>),

	/// The grow instruction.
	///
	/// Fields:
	/// 0. The raw bits of the immediate.
	Grow(Bits<8, false>),

	/// Trap instruction.
	Trap,

	/// The cast instruction.
	///
	/// Fields:
	/// 0. The type to cast to.
	/// 0. Output offset.
	Cast(Bits<4, false>, Bits<5, false>),
}

impl Instruction
{
	/// Returns the output references of all outputs of this instruction.
	///
	/// Each value is an output offset, where 0 is an output to the next
	/// instruction, 1 is to the second instructions and so on. May have
	/// multiple outputs to the same instruction. Does not guarantee that the
	/// number of outputs is equal the length of the returned array.
	/// E.g., the call instruction will only have 1 output reference, even if it
	/// returns multiple values.
	///
	/// The order is not meaningful
	pub fn out_refs(&self) -> Vec<usize>
	{
		use Instruction::*;
		match self
		{
			Invalid(_) | Jump(_, _) | Trap | Store | StoreStack(_) | NoOp | StackRes(_, _, _) =>
			{
				vec![]
			},

			Duplicate(n, o1, o2) | Echo(n, o1, o2) =>
			{
				let mut res = vec![o1.value as usize, o2.value as usize];
				if *n
				{
					res.push(0);
				}
				res
			},
			EchoLong(o) => vec![o.value as usize],
			Alu(_, o) | Pick(o) | PickI(_, o) | Cast(_, o) => vec![o.value as usize],
			Alu2(_, ot, o) =>
			{
				let mut res = vec![o.value as usize];
				if matches!(ot, Alu2OutputVariant::HighNext | Alu2OutputVariant::LowNext)
				{
					res.push(0);
				}
				res
			},
			Call(_, _)
			| Load(_, _)
			| LoadStack(_, _)
			| StackAddr(_, _)
			| Constant(_, _)
			| Grow(_) => vec![0],
		}
	}
}

#[cfg(test)]
mod test
{
	use crate::{Alu2OutputVariant, Instruction};
	use quickcheck_macros::quickcheck;

	/// Tests Instruction::out_refs returns the correct number of references.
	#[quickcheck]
	fn out_refs_count(inst: Instruction)
	{
		use crate::Instruction::*;
		let expected_count = match inst
		{
			Invalid(_) | Jump(_, _) | Trap | Store | StoreStack(_) | NoOp | StackRes(_, _, _) => 0,

			Duplicate(n, _, _) | Echo(n, _, _) =>
			{
				if n
				{
					3
				}
				else
				{
					2
				}
			},
			EchoLong(_)
			| Alu(_, _)
			| Pick(_)
			| PickI(_, _)
			| Cast(_, _)
			| Call(_, _)
			| Load(_, _)
			| LoadStack(_, _)
			| StackAddr(_, _)
			| Constant(_, _)
			| Grow(_) => 1,
			Alu2(_, ot, _) =>
			{
				if matches!(ot, Alu2OutputVariant::HighNext | Alu2OutputVariant::LowNext)
				{
					2
				}
				else
				{
					1
				}
			},
		};
		assert_eq!(expected_count, inst.out_refs().len());
	}
}
