use duplicate::{duplicate, duplicate_inline};
use num_traits::int::PrimInt;
use quickcheck::{empty_shrinker, Arbitrary, Gen};
use scry_isa::{
	Alu2OutputVariant, Alu2Variant, AluVariant, Bits, CallVariant, Instruction, Parser,
	StackControlVariant,
};
use std::{collections::HashMap, fmt::Debug};

#[derive(Debug, Clone)]
pub struct Arb<T>(pub T);
impl<T> Arb<T>
where
	Self: Arbitrary,
{
	/// Constructs an arbitrary `T` and returns it.
	pub fn arb_inner(g: &mut Gen) -> T
	{
		Self::arbitrary(g).0
	}
}

/// Generates arbitrary numbers within the range [low, high[.
fn gen_range<T: Arbitrary + PrimInt>(g: &mut Gen, low: T, high: T) -> T
{
	let base = T::arbitrary(g);
	let diff = high - low;
	let modulo = base % diff;
	modulo + if modulo < T::zero() { high } else { low }
}

impl<const N: u32, const SIGNED: bool> Arbitrary for Arb<Bits<N, SIGNED>>
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		Self(Bits {
			value: gen_range(
				g,
				Bits::<N, SIGNED>::min().value,
				Bits::<N, SIGNED>::max().value + 1,
			),
		})
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		Box::new(self.0.value.shrink().map(|v| Self(Bits::new(v).unwrap())))
	}
}

impl Arbitrary for Arb<Instruction>
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		use Instruction::*;
		Self(match gen_range(g, 0, Instruction::VARIANT_COUNT)
		{
			0 => Jump(Arb::arb_inner(g), Arb::arb_inner(g)),
			1 => Call(Arb::arb_inner(g), Arb::arb_inner(g)),
			2 =>
			{
				Echo(
					Arbitrary::arbitrary(g),
					Arb::arb_inner(g),
					Arb::arb_inner(g),
				)
			},
			3 => EchoLong(Arb::arb_inner(g)),
			4 => Alu(Arb::arb_inner(g), Arb::arb_inner(g)),
			5 => Alu2(Arb::arb_inner(g), Arb::arb_inner(g), Arb::arb_inner(g)),
			6 =>
			{
				Duplicate(
					Arbitrary::arbitrary(g),
					Arb::arb_inner(g),
					Arb::arb_inner(g),
				)
			},
			7 => Capture(Arb::arb_inner(g), Arb::arb_inner(g)),
			8 => Pick(Arb::arb_inner(g)),
			9 => PickI(Arb::arb_inner(g), Arb::arb_inner(g)),
			10 => Load(Arbitrary::arbitrary(g), Arb::arb_inner(g)),
			11 => Store,
			12 => Value(Arb::arb_inner(g)),
			13 => Invalid(0),
			x => panic!("Missing arbitrary implement for instruction: {}", x),
		})
	}
}

duplicate_inline! {
	[name;[AluVariant];[Alu2Variant];[Alu2OutputVariant];[CallVariant];[StackControlVariant];]
	impl Arbitrary for Arb<name>
	{
		fn arbitrary(g: &mut Gen) -> Self {
			Self(g.choose(&name::ALL_VARIANTS).unwrap().clone())
		}
	}
}

/// An arbitrary valid symbol.
pub type ArbSymbol = Arb<String>;
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

		Box::new(result.into_iter().filter(|Arb(s)| {
			let c = s.chars().nth(0).unwrap();
			!c.is_numeric()
		}))
	}
}

/// Arbitrary output reference e.g. "=>branch=>branch_to=>target"
/// Each element is the symbol and its address for each link.
/// E.g. [("branch", 10), ("branch_to", 20), ("target", 30)]
pub type ArbReference = Arb<Vec<(Arb<String>, i32)>>;
impl Arbitrary for ArbReference
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		let mut result = Vec::<Arb<String>>::arbitrary(g);
		// Ensure there is at least 1
		result.push(Arbitrary::arbitrary(g));
		Self(
			result
				.into_iter()
				.enumerate()
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

/// Returns the indices of offset operands, e.g., the 1 in "jmp x"
fn offset_index(instr: &Instruction) -> impl Iterator<Item = usize>
{
	use Instruction::*;
	match instr
	{
		Jump(..) => [1, 2].iter(),
		Call(..) => [1].iter(),
		// We don't use the wildcard match to not forget to add instructions above
		Echo(..) | EchoLong(..) | Alu(..) | Alu2(..) | Duplicate(..) | Capture(..) | Pick(..)
		| PickI(..) | Load(..) | Store | Value(..) | Invalid(..) => [].iter(),
	}
	.cloned()
}

#[duplicate(
	name					ref_type(inner);
	[get_offset_value]		[& inner];
	[get_offset_value_mut]	[&mut inner];
)]
fn name(instr: ref_type([Instruction]), idx: usize) -> ref_type([i32])
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
fn references(instr: &Instruction) -> impl Iterator<Item = (usize, i32)>
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
		Jump(..) | Call(..) | Load(..) | Store | Value(..) | Invalid(..) => vec![],
	}
	.into_iter()
}

#[duplicate(
	name						ref_type(inner);
	[get_reference_value]		[& inner];
	[get_reference_value_mut]	[&mut inner];
)]
fn name(instr: ref_type([Instruction]), idx: usize) -> ref_type([i32])
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

/// An instruction in assembly format.
#[derive(Clone, Debug)]
pub(crate) struct AssemblyInstruction(pub Instruction, pub Vec<(usize, OperandSubstitution)>);
impl Arbitrary for AssemblyInstruction
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		let instruction = Arb::arbitrary(g).0;
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
					substitutions.push((idx, OperandSubstitution::Ref(Arb(vec![]))));
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
					substitutions.push((idx, OperandSubstitution::Ref(Arb(result_refs))))
				}
			}
		}
		Self(instruction, substitutions)
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		let mut result = Vec::new();

		for i in 0..self.1.len()
		{
			let mut substitutions = self.1.clone();
			let (removed_idx, removed_sub) = substitutions.remove(i);

			// shrink by removing a substitution
			result.push(Self(self.0.clone(), substitutions.clone()));

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
						result.push(Self(instr_clone, subs));
					});
				},
				OperandSubstitution::Ref(Arb(ref refs)) =>
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
								subs.push((removed_idx, OperandSubstitution::Ref(Arb(refs_clone))));
								result.push(Self(instr_clone, subs));
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
						subs.push((removed_idx, OperandSubstitution::Ref(Arb(refs_clone))));
						result.push(Self(instr_clone, subs));
					}
				},
			}

			// Shrink by shrinking a symbol (from the removed offset/reference)
			removed_sub.shrink().for_each(|sym| {
				let mut subs = substitutions.clone();
				subs.push((removed_idx, sym));
				result.push(Self(self.0.clone(), subs));
			})
		}

		Box::new(result.into_iter())
	}
}
impl AssemblyInstruction
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
				OperandSubstitution::Offset(Arb(sym)) =>
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
				OperandSubstitution::Ref(Arb(symbols)) =>
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

/// Represents the different ways separator character sequences (",", "=>",
/// etc.) can be in separate tokens
#[derive(Clone, Copy, Debug)]
pub enum SeparatorType
{
	/// The separator is at the end of a token with other text preceding it.
	AtEnd,
	/// The separator is at the start of a token with other text succeeding it.
	AtStart,
	/// The separator is in the middle of a token with text both preding and
	/// succeeding it.
	InMiddle,
	/// The separator is alone in the token, with no other text.
	Alone,
}
impl Arbitrary for SeparatorType
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		use SeparatorType::*;
		*g.choose(&[AtEnd, AtStart, InMiddle, Alone]).unwrap()
	}
}
