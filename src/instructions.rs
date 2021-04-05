use duplicate::duplicate;

/// Represents a set of N bits.
#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub struct Bits<const N: u32> {
	value: i32
}

impl<const N: u32> Bits<N> {
	
	#[duplicate(
	name max min value_type;
	[new_unsigned] [max_unsigned] [min_unsigned] [u16];
	[new_signed] [max_signed] [min_signed] [i16];
	
	)]
	/// Constructs a new Bits with given value.
	///
	/// If the value isn't within a valid range None is returned.
	pub fn name(value: value_type) -> Option<Self> {
		if Self::max().value() >= value as i32 &&
			Self::min().value() <= value as i32 {
			Some(Self{value: value as i32})
		} else {
			None
		}
	}
	
	pub fn value(&self) -> i32 {
		self.value
	}
	
	pub fn saturated() -> Self {
		Self{value: ( 2i32.pow(N)) - 1}
	}
	
	pub fn cleared() -> Self {
		Self{value: 0}
	}
	
	pub fn max_unsigned() -> Self {
		Self::saturated()
	}
	
	pub fn min_unsigned() -> Self {
		Self::cleared()
	}
	
	pub fn max_signed() -> Self {
		Self{value: ( 2i32.pow(N)/2) - 1}
	}
	
	pub fn min_signed() -> Self {
		Self{value: ( 2i32.pow(N)/2) * -1}
	}
}

/// Variants of the call instruction
#[derive(Debug)]
pub enum CallVariant {
	Call, Portal, Ret, Trap
}

#[derive(Debug)]
pub enum StackControlVariant {
	Reserve, Free
}

/// All instructions
#[derive(Debug)]
pub enum Instruction {
	/// The jump instruction.
	///
	/// Fields:
	/// 0. The branch target offset.
	/// 0. The branch location offset.
	Jump(Bits<7>,Bits<6>),
	
	/// load instruction.
	///
	/// Fields
	/// 0. Whether the loaded value is signed.
	/// 0. The length of the loaded value.
	/// 0. The size of the loaded value.
	/// 0. Whether the primary address space is the target.
	/// 0. The "ar" flags.
	Load(bool, Bits<3>, Bits<3>,bool, Bits<2>),
	
	/// The echo instruction.
	///
	/// Fields:
	/// 0. Output target 1.
	/// 0. Output target 2.
	/// 0. Whether the remaining inputs should be output to the the next instruction.
	Echo(Bits<5>, Bits<5>, bool),
	
	/// The ALU instruction.
	///
	/// Fields:
	/// 0. Output target.
	/// 0. Function specifier.
	/// 0. Modifier.
	Alu(Bits<5>, Bits<4>, Bits<3>),
	
	/// The call instruction.
	///
	/// Fields:
	/// 0. The variant.
	/// 0. The branch location offset.
	Call(CallVariant, Bits<6>),
	
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