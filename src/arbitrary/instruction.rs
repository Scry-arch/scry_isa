use crate::{
	arbitrary::*, Alu2OutputVariant, Alu2Variant, AluVariant, CallVariant, Instruction, Parser,
	StackControlVariant,
};
use duplicate::duplicate_inline;
use quickcheck::{Arbitrary, Gen};
use std::{collections::HashMap, marker::PhantomData};

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
			10 => Load(Arbitrary::arbitrary(g), Arbitrary::arbitrary(g)),
			11 => Store,
			12 => Value(Arbitrary::arbitrary(g)),
			13 => Invalid(0),
			x => panic!("Missing arbitrary implement for instruction: {}", x),
		}
	}
}

duplicate_inline! {
	[name;[AluVariant];[Alu2Variant];[Alu2OutputVariant];[CallVariant];[StackControlVariant];]
	impl Arbitrary for name
	{
		fn arbitrary(g: &mut Gen) -> Self {
			g.choose(&name::ALL_VARIANTS).unwrap().clone()
		}
	}
}

/// Trait for arbitrary-instruction-generating structs
pub trait ArbInstruction: Arbitrary
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

/// An instruction in assembly format.
///
/// Can provide a generic type that restricts which instruction are generated.
#[derive(Clone, Debug)]
pub struct AssemblyInstruction<I: ArbInstruction = Instruction>(
	pub Instruction,
	pub Vec<(usize, OperandSubstitution)>,
	PhantomData<I>,
);
impl<I: ArbInstruction> Arbitrary for AssemblyInstruction<I>
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		let instruction = I::arbitrary(g).extract();
		let mut substitutions = Vec::new();
		// Replace integer offsets with symbols
		for idx in offset_index(&instruction)
		{
			// Sometimes keep the integer offset
			if bool::arbitrary(g)
			{
				substitutions.push((idx, OperandSubstitution::Offset(Arbitrary::arbitrary(g))))
			}
		}

		// Replace integer output references with symbols
		for (idx, value) in references(&instruction)
		{
			// Sometimes keep the integer references
			if bool::arbitrary(g)
			{
				if value == 0 && bool::arbitrary(g)
				{
					// Sometimes omit the symbol for referencing the next instruction
					// i.e. "=>0" becomes "=>"
					substitutions.push((idx, OperandSubstitution::Ref(ArbReference(vec![]))));
				}
				else
				{
					let mut result_refs = Vec::new();
					let first_offset = gen_range(g, 0, value + 1);
					result_refs.push((Arbitrary::arbitrary(g), (1 + first_offset) * 2));

					let mut value_left = value - first_offset;
					let mut last_address: i32 = result_refs[0].1;
					let mut next_branch_to = true;

					while value_left > 0
					{
						if next_branch_to
						{
							last_address =
								gen_range(g, i32::MIN / 2, (i32::MAX / 2) - value_left) * 2;
						}
						else
						{
							let next_offset = gen_range(g, 1, 1 + value_left);
							last_address += next_offset * 2;
							value_left -= next_offset;
						}
						result_refs.push((Arbitrary::arbitrary(g), last_address));
						next_branch_to = !next_branch_to;
					}
					substitutions.push((idx, OperandSubstitution::Ref(ArbReference(result_refs))))
				}
			}
		}
		Self(instruction, substitutions, PhantomData)
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		let mut result = Vec::new();

		for i in 0..self.1.len()
		{
			let mut substitutions = self.1.clone();
			let (removed_idx, removed_sub) = substitutions.remove(i);

			// shrink by removing a substitution
			result.push(Self(self.0.clone(), substitutions.clone(), PhantomData));

			match removed_sub
			{
				OperandSubstitution::Offset(ref sym) =>
				{
					// Shrink by shrinking the offset
					let mut tmp_clone = self.0.clone();
					let offset = *get_offset_value(&mut tmp_clone, removed_idx);
					offset.shrink().for_each(|o| {
						let mut instr_clone = self.0.clone();
						*get_offset_value_mut(&mut instr_clone, removed_idx) = o;

						let mut subs = substitutions.clone();
						subs.push((removed_idx, OperandSubstitution::Offset(sym.clone())));
						result.push(Self(instr_clone, subs, PhantomData));
					});
				},
				OperandSubstitution::Ref(ArbReference(ref refs)) =>
				{
					if refs.len() > 0
					{
						// Shrink by shrinking the last link offset
						if refs.len() % 2 != 0
						{
							// The last link is an offset
							let mut refs_clone = refs.clone();
							let (removed_sym, removed_address) = refs_clone.pop().unwrap();

							let previous_address = refs_clone.last().map_or(0, |(_, a)| *a);

							let offset = ((removed_address - previous_address) / 2) - 1;
							offset.shrink().for_each(|o| {
								let mut instr_clone = self.0.clone();
								let mut refs_clone = refs_clone.clone();

								refs_clone
									.push((removed_sym.clone(), previous_address + 2 + (o * 2)));
								*get_reference_value_mut(&mut instr_clone, removed_idx) -=
									offset - o;

								let mut subs = substitutions.clone();
								subs.push((
									removed_idx,
									OperandSubstitution::Ref(ArbReference(refs_clone)),
								));
								result.push(Self(instr_clone, subs, PhantomData));
							});
						}

						// shrink by removing a reference link
						let mut instr_clone = self.0.clone();
						let mut refs_clone = refs.clone();
						let (_, removed_address) = refs_clone.pop().unwrap();

						if refs.len() % 2 != 0
						{
							// The last link is an offset
							let previous_address = refs_clone.last().map_or(0, |(_, a)| *a);
							*get_reference_value_mut(&mut instr_clone, removed_idx) -=
								((removed_address-previous_address)/2)
										// If removing the last link, need to
										// simulate target is address 2
										- (refs.len() == 1) as i32;
						}
						let mut subs = substitutions.clone();
						subs.push((
							removed_idx,
							OperandSubstitution::Ref(ArbReference(refs_clone)),
						));
						result.push(Self(instr_clone, subs, PhantomData));
					}
				},
			}

			// Shrink by shrinking a symbol (from the removed offset/reference)
			removed_sub.shrink().for_each(|sym| {
				let mut subs = substitutions.clone();
				subs.push((removed_idx, sym));
				result.push(Self(self.0.clone(), subs, PhantomData));
			})
		}

		Box::new(result.into_iter())
	}
}
impl<I: ArbInstruction> AssemblyInstruction<I>
{
	/// Returns the assembly instruction and a resolver for any symbols.
	pub fn tokens_and_resolver(&self) -> (String, impl Fn(Option<&str>, &str) -> i32)
	{
		let mut buffer = String::new();
		Instruction::print(&self.0, &mut buffer).unwrap();
		let mut tokens: Vec<_> = buffer
			.split_ascii_whitespace()
			.map(|t| String::from(t))
			.collect();

		let mut symbol_addresses = HashMap::new();

		for (idx, substitution) in self.1.iter()
		{
			match substitution
			{
				OperandSubstitution::Offset(ArbSymbol(sym)) =>
				{
					// Extract offset value
					let split =
						tokens[*idx].split_at(tokens[*idx].find(",").unwrap_or(tokens[*idx].len()));
					let offset_value = *get_offset_value(&self.0, *idx);

					// replace offset with symbol
					let mut replacement = sym.clone();
					let symbol_address = match self.0
					{
						Instruction::Jump(_, second) if *idx == 1 && offset_value > 0 =>
						{
							(second.value() + 1 + offset_value) * 2
						},
						_ => (offset_value + ((offset_value >= 0) as i32)) * 2,
					};
					symbol_addresses.insert(replacement.clone(), symbol_address);

					// Add separators after offset value
					replacement.push_str(split.1);
					tokens[*idx] = replacement;
				},
				OperandSubstitution::Ref(ArbReference(symbols)) =>
				{
					// Extract reference value
					let split = tokens[*idx]
							// remove the preceding '=>'
							.split_at(2).1
							// potentially remove ',' at end
							.split_at(tokens[*idx].find(",").unwrap_or(tokens[*idx].len())-2);

					// replace reference with symbols
					let mut replacement = String::new();
					if symbols.len() == 0
					{
						replacement.push_str("=>");
					}
					else
					{
						for (sym, address) in symbols.iter()
						{
							replacement.push_str("=>");
							replacement.push_str(sym.0.as_str());
							symbol_addresses.insert(sym.0.clone(), *address);
						}
					}
					// Add separators after reference value
					replacement.push_str(split.1);
					tokens[*idx] = replacement.clone();
				},
			}
		}

		let mut assembly = String::new();
		for t in tokens
		{
			assembly.push_str(t.as_str());
			assembly.push(' ');
		}

		(assembly, move |start, end| {
			let resolve = |sym| {
				symbol_addresses
					.iter()
					.find_map(|(t, a)| {
						if t.as_str() == sym
						{
							Some(*a)
						}
						else
						{
							None
						}
					})
					.unwrap_or_else(|| panic!("Unknown symbol: {}", sym))
			};
			let start = start.map(resolve).unwrap_or(0);
			resolve(end) - start
		})
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
		Self(match gen_range(g, 0, 8)
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
			_ => unreachable!(),
		})
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		Box::new(self.0.shrink().map(|i| Self(i)))
	}
}
