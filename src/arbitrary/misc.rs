use crate::{arbitrary::*, BitValue, Bits, Instruction};
use duplicate::duplicate_item;
use quickcheck::{empty_shrinker, Arbitrary, Gen};
use std::convert::TryInto;

impl<const N: u32, const SIGNED: bool> Arbitrary for Bits<N, SIGNED>
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		Bits {
			value: gen_range(
				g,
				Bits::<N, SIGNED>::get_min().value,
				Bits::<N, SIGNED>::get_max().value + 1,
			),
		}
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		Box::new(self.value.shrink().map(|v| v.try_into().unwrap()))
	}
}

/// Returns the indices of offset operands, e.g., the 1 in "jmp x"
pub fn offset_index(instr: &Instruction) -> impl Iterator<Item = usize>
{
	use Instruction::*;
	match instr
	{
		Jump(..) => [1, 2].iter(),
		Call(..) => [1].iter(),
		// We don't use the wildcard match to not forget to add instructions above
		Echo(..) | EchoLong(..) | Alu(..) | Alu2(..) | Duplicate(..) | Capture(..) | Pick(..)
		| PickI(..) | Load(..) | Store | Request(..) | Invalid(..) | Nop => [].iter(),
	}
	.cloned()
}

#[duplicate_item(
	name					ref_type(inner);
	[get_offset_value]		[& inner];
	[get_offset_value_mut]	[&mut inner];
)]
pub fn name(instr: ref_type([Instruction]), idx: usize) -> ref_type([i32])
{
	use Instruction::*;
	let instruction_clone = instr.clone();
	match instr
	{
		Jump(first, _) if idx == 1 => ref_type([first.value]),
		Jump(_, second) if idx == 2 => ref_type([second.value]),
		Call(_, b) if idx == 1 => ref_type([b.value]),
		_ =>
		{
			panic!(
				"Invalid reference index '{}' for instruction '{:?}'",
				idx, instruction_clone
			)
		},
	}
}

/// Returns the indices of output reference operands, e.g., 1 in "add =>2"
/// and their integer value in the instruction
pub fn references(instr: &Instruction) -> impl Iterator<Item = (usize, i32)>
{
	use Instruction::*;
	match instr
	{
		Echo(_, first, second) | Duplicate(_, first, second) | Capture(first, second) =>
		{
			vec![(1, first.value()), (2, second.value())]
		},
		EchoLong(b) => vec![(1, b.value())],
		Pick(b) => vec![(1, b.value())],
		PickI(_, b) => vec![(2, b.value())],
		Alu(_, b) => vec![(1, b.value())],
		Alu2(_, _, b) => vec![(2, b.value())],
		// We don't use the wildcard match to not forget to add instructions above
		Jump(..) | Call(..) | Load(..) | Store | Request(..) | Invalid(..) | Nop => vec![],
	}
	.into_iter()
}

#[duplicate_item(
name						ref_type(inner);
[get_reference_value]		[& inner];
[get_reference_value_mut]	[&mut inner];
)]
pub fn name(instr: ref_type([Instruction]), idx: usize) -> ref_type([i32])
{
	use Instruction::*;
	let instruction_clone = instr.clone();
	match instr
	{
		Echo(_, first, _) if idx == 1 => ref_type([first.value]),
		Echo(_, _, second) if idx == 2 => ref_type([second.value]),
		EchoLong(b) if idx == 1 => ref_type([b.value]),
		Duplicate(_, first, _) if idx == 1 => ref_type([first.value]),
		Duplicate(_, _, second) if idx == 2 => ref_type([second.value]),
		Capture(first, _) if idx == 1 => ref_type([first.value]),
		Capture(_, second) if idx == 2 => ref_type([second.value]),
		Alu(_, b) if idx == 1 => ref_type([b.value]),
		Alu2(_, _, b) if idx == 2 => ref_type([b.value]),
		_ =>
		{
			panic!(
				"Invalid reference index '{}' for instruction '{:?}'",
				idx, instruction_clone
			)
		},
	}
}

/// An arbitrary valid symbol.
#[derive(Clone, Debug)]
pub struct ArbSymbol(pub String);
impl Arbitrary for ArbSymbol
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		const SYMBOL_CHARS: &'static str =
			"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_.";

		let size = gen_range(g, 1, g.size());
		let mut result = String::new();

		// First character cannot be numeric
		result.push(
			SYMBOL_CHARS
				.chars()
				.nth(gen_range(g, 10, SYMBOL_CHARS.len()))
				.unwrap(),
		);

		for _ in 1..size
		{
			result.push(
				SYMBOL_CHARS
					.chars()
					.nth(gen_range(g, 0, SYMBOL_CHARS.len()))
					.unwrap(),
			);
		}
		Self(result)
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		if self.0.len() == 1
		{
			return empty_shrinker();
		}

		let mut result = Vec::new();

		for i in 0..self.0.len()
		{
			let mut copy = self.0.clone();
			copy.remove(i);
			result.push(Self(copy));
		}

		Box::new(result.into_iter().filter(|ArbSymbol(s)| {
			let c = s.chars().nth(0).unwrap();
			!c.is_numeric()
		}))
	}
}

/// Arbitrary output reference e.g. "=>branch=>branch_to=>target"
/// Each element is the symbol and its address for each link.
/// E.g. [("branch", 10), ("branch_to", 20), ("target", 30)]
#[derive(Clone, Debug)]
pub struct ArbReference(pub Vec<(ArbSymbol, i32)>);
impl Arbitrary for ArbReference
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		let mut result = Vec::<ArbSymbol>::arbitrary(g);
		// Ensure there is at least 1
		result.push(Arbitrary::arbitrary(g));
		Self(
			result
				.into_iter()
				.enumerate()
				// Placeholder addresses
				.map(|(i, s)| (s, ((i + 1) * 2) as i32))
				.collect::<Vec<_>>(),
		)
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		let mut result: Vec<_> = Vec::new();

		// Shrink by shrinking symbol names
		result.extend(self.0.iter().enumerate().flat_map(|(i, (sym, address))| {
			sym.shrink().map(move |sym| {
				let mut clone = self.0.clone();
				clone[i] = (sym, *address);
				clone
			})
		}));

		Box::new(result.into_iter().map(|vec| Self(vec)))
	}
}

/// Substitutions for operands using symbols.
#[derive(Clone, Debug)]
pub enum OperandSubstitution
{
	/// Substituting address offset operands with a symbol
	/// E.g. "jmp 10" => "jmp branch_location"
	Offset(ArbSymbol),

	/// Substituting output reference operands with symbol chains
	/// E.g. "add =>10" => "add =>branch=>branch_to=>target"
	Ref(ArbReference),
}
impl Arbitrary for OperandSubstitution
{
	fn arbitrary(_: &mut Gen) -> Self
	{
		unimplemented!()
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		use OperandSubstitution::*;
		match self
		{
			Offset(s) => Box::new(s.shrink().map(|s| Offset(s))),
			Ref(s) => Box::new(s.shrink().map(|s| Ref(s))),
		}
	}
}
