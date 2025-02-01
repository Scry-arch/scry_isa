use crate::{arbitrary::*, BitValue, Bits, BitsDyn, Instruction, Parser, Resolve};
use duplicate::duplicate_item;
use quickcheck::{empty_shrinker, Arbitrary, Gen};
use std::{collections::HashMap, convert::TryInto, marker::PhantomData};

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
impl<const N: u32> Arbitrary for BitsDyn<N>
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		if bool::arbitrary(g)
		{
			Bits::<N, true>::arbitrary(g).into()
		}
		else
		{
			Bits::<N, false>::arbitrary(g).into()
		}
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		let mut result: Vec<Self> = Vec::new();
		if self.is_signed()
		{
			let bits: Bits<N, true> = self.clone().try_into().unwrap();
			result.extend(bits.shrink().map(|b| Self::from(b)));

			// Add an unsigned version too
			let bits: Bits<N, false> = bits.into();
			result.push(bits.into());
		}
		else
		{
			let bits: Bits<N, false> = self.clone().try_into().unwrap();
			result.extend(bits.shrink().map(|b| Self::from(b)));
		}

		Box::new(result.into_iter())
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
		| PickI(..) | Load(..) | Store(..) | NoOp | Request(..) | Invalid(..) | Constant(..)
		| StackAddr(..) | StackRes(..) => [].iter(),
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
		Jump(..) | Call(..) | Load(..) | Store(..) | NoOp | Request(..) | Invalid(..)
		| Constant(..) | StackAddr(..) | StackRes(..) =>
		{
			vec![]
		},
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
		Pick(first) if idx == 1 => ref_type([first.value]),
		PickI(_, second) if idx == 2 => ref_type([second.value]),
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

/// Type of substitution
#[derive(Clone, Debug)]
pub enum SubType
{
	/// Output offset e.g. "13" becomes "label1"
	Offset(ArbSymbol),

	/// Output reference e.g. "=>branch=>branch_to=>target"
	///
	/// If none, it means its a call argument flag (=>|=>).
	Ref(Vec<Option<ArbSymbol>>),
}
impl SubType
{
	pub fn uses_symbol(&self, sym: &ArbSymbol) -> bool
	{
		match self
		{
			SubType::Offset(s) => sym.0 == s.0,
			SubType::Ref(v) =>
			{
				v.iter()
					.filter(|s| s.is_some())
					.any(|s| s.as_ref().unwrap().0 == sym.0)
			},
		}
	}

	pub fn replace_uses(&mut self, to_replace: &ArbSymbol, with: ArbSymbol)
	{
		match self
		{
			SubType::Offset(s) if s.0 == to_replace.0 => *s = with,
			SubType::Ref(v) =>
			{
				v.iter_mut()
					.filter(|s| s.is_some() && s.as_ref().unwrap().0 == to_replace.0)
					.for_each(|s| *s.as_mut().unwrap() = with.clone())
			},
			_ => (),
		}
	}
}

/// Substitutions for operands using symbols.
#[derive(Clone, Debug)]
pub struct OperandSubstitutions
{
	/// Map of substitutions from the index of the token in assembly
	/// to the substitution.
	pub subs: HashMap<usize, SubType>,

	/// The addresses of the symbols used for substitutions.
	pub symbol_addrs: HashMap<String, i32>,
}
impl OperandSubstitutions
{
	/// Creates a substitution for the given index operand as a reference,
	/// with each symbol given with its address.
	///
	/// Assumes all symbols are unique (no duplicates).
	pub fn from_reference(idx: usize, refs: Vec<Option<(&str, i32)>>) -> Self
	{
		let mut result = Self {
			subs: HashMap::new(),
			symbol_addrs: HashMap::new(),
		};
		let mut sub_refs = Vec::new();

		refs.into_iter().for_each(|entry| {
			sub_refs.push(entry.map(|(sym, addr)| {
				result.symbol_addrs.insert(sym.to_string(), addr);
				ArbSymbol(sym.to_string())
			}));
		});
		result.subs.insert(idx, SubType::Ref(sub_refs));

		result
	}

	/// Whether any substitutions uses the given symbol.
	fn uses_symbol(&self, sym: &ArbSymbol) -> bool
	{
		self.uses_symbol_string(&sym.0)
	}

	/// Whether any substitutions uses the given string in a symbol.
	fn uses_symbol_string(&self, uses: &String) -> bool
	{
		self.subs.iter().any(|(_, sub)| {
			match sub
			{
				SubType::Offset(sym) => sym.0 == *uses,
				SubType::Ref(refs) =>
				{
					refs.iter()
						.filter_map(|link| link.as_ref())
						.any(|sym| sym.0 == *uses)
				},
			}
		})
	}

	/// Creates an arbitrary symbol that is not already in used in a
	/// substitution.
	fn arb_unique_symbol(&self, g: &mut Gen) -> ArbSymbol
	{
		loop
		{
			let new_sym = ArbSymbol::arbitrary(g);
			if !self.uses_symbol(&new_sym)
			{
				break new_sym;
			}
		}
	}

	/// Gets the address of the given symbol.
	fn address_of(&self, sym: &ArbSymbol) -> i32
	{
		self.symbol_addrs[&sym.0]
	}

	/// Changes the given symbol's address (assumes symbol is present)
	fn change_address_of(&mut self, sym: &ArbSymbol, addr: i32)
	{
		*self.symbol_addrs.get_mut(&sym.0).unwrap() = addr;
	}

	/// Removes any symbols from the address map that isn't used in a
	/// substitution.
	fn clean_addrs(&mut self)
	{
		let unused = self
			.symbol_addrs
			.iter()
			.filter(|(s, _)| !self.uses_symbol_string(*s))
			.map(|(s, _)| s.clone())
			.collect::<Vec<_>>();
		unused.into_iter().for_each(|s| {
			self.symbol_addrs.remove(&s);
		});
	}

	/// Returns the required address a symbol to substitute the offset at the
	/// given index.
	fn instruction_offset_address(instruction: &Instruction, idx: usize) -> i32
	{
		let offset_value = *get_offset_value(instruction, idx);
		match instruction
		{
			Instruction::Jump(_, second) if idx == 1 && offset_value > 0 =>
			{
				(second.value() + 1 + offset_value) * 2
			},
			_ => (offset_value + ((offset_value >= 0) as i32)) * 2,
		}
	}

	/// Creates arbitrary substitutions for the given instruction.
	pub fn arbitrary_from(g: &mut Gen, instruction: &Instruction) -> Self
	{
		let mut result = Self {
			subs: HashMap::new(),
			symbol_addrs: HashMap::new(),
		};

		// Replace integer offsets with symbols
		for idx in offset_index(instruction)
		{
			// Sometimes keep the integer offset
			if u8::arbitrary(g) % 10 > 8
			{
				let new_sym = result.arb_unique_symbol(g);
				result.subs.insert(idx, SubType::Offset(new_sym.clone()));
				let symbol_address = Self::instruction_offset_address(instruction, idx);
				result.symbol_addrs.insert(new_sym.0, symbol_address);
			}
		}

		// Replace integer output references with symbols
		for (idx, value) in references(&instruction)
		{
			// Sometimes keep the integer references
			if u8::arbitrary(g) % 10 > 8
			{
				if value == 0 && bool::arbitrary(g)
				{
					// Sometimes omit the symbol for referencing the next instruction
					// i.e. "=>0" becomes "=>"
					result.subs.insert(idx, SubType::Ref(vec![]));
				}
				else
				{
					result.subs.insert(idx, SubType::Ref(Vec::new()));
					let push_sym = |op_subs: &mut OperandSubstitutions, sym| {
						let SubType::Ref(ref mut refs) = op_subs.subs.get_mut(&idx).unwrap()
						else
						{
							unreachable!()
						};
						refs.push(sym);
					};
					let insert_penultimate_sym = |op_subs: &mut OperandSubstitutions, sym| {
						let SubType::Ref(ref mut refs) = op_subs.subs.get_mut(&idx).unwrap()
						else
						{
							unreachable!()
						};
						refs.insert(refs.len() - 1, sym);
					};
					// 50% chance of needing a jump
					let first_offset = if bool::arbitrary(g)
					{
						value
					}
					else
					{
						gen_range(g, 0, value + 1)
					};
					let new_sym = result.arb_unique_symbol(g);
					let new_addr = (1 + first_offset) * 2;
					result.symbol_addrs.insert(new_sym.0.clone(), new_addr);
					push_sym(&mut result, Some(new_sym));

					let mut offset_count = first_offset;
					let mut last_address = new_addr;
					let mut last_was_offset = true;

					while offset_count < value
					{
						let value_left = value - offset_count;
						if last_was_offset
						{
							// 10% chance of adding call argument flag, otherwise a jump
							if u8::arbitrary(g) % 10 == 0
							{
								// argument flags can only split an offset, so add one before the
								// last offset
								insert_penultimate_sym(&mut result, None);
								offset_count += 1;
							}
							else
							{
								last_address = gen_range(g, 0, (i32::MAX / 2) - value_left) * 2;
								let new_sym = result.arb_unique_symbol(g);
								result.symbol_addrs.insert(new_sym.0.clone(), last_address);

								push_sym(&mut result, Some(new_sym));
								last_was_offset = false;
							}
						}
						else
						{
							// Last was either a jump or a call argument flag, next must therefore
							// be offset 50% chance of not using all value, so need more links
							let next_offset = if bool::arbitrary(g)
							{
								value_left
							}
							else
							{
								gen_range(g, 1, value_left + 1)
							};
							last_address += next_offset * 2;
							offset_count += next_offset;
							last_was_offset = true;
							let new_sym = result.arb_unique_symbol(g);
							result.symbol_addrs.insert(new_sym.0.clone(), last_address);
							push_sym(&mut result, Some(new_sym))
						}
						assert!(last_address >= 0);
					}
					assert_eq!(offset_count, value);
				}
			}
		}

		result
	}
}

/// An instruction in assembly format.
///
/// Can provide a generic type that restricts which instruction are generated.
#[derive(Clone, Debug)]
pub struct AssemblyInstruction<I: ArbInstruction = Instruction>
{
	/// Instruction represented by the assembly
	pub instruction: Instruction,

	/// Substitutions of the operands in the associated instruction
	pub substitutions: OperandSubstitutions,
	pub phantom: PhantomData<I>,
}
impl<I: ArbInstruction> AssemblyInstruction<I>
{
	/// Returns the assembly instruction and a resolver for any symbols.
	pub fn tokens_and_resolver(&self) -> (String, impl Fn(Resolve) -> Result<i32, &'_ str>)
	{
		let mut buffer = String::new();
		Instruction::print(&self.instruction, &mut buffer).unwrap();
		let mut tokens: Vec<_> = buffer
			.split_ascii_whitespace()
			.map(|t| String::from(t))
			.collect();

		for (idx, substitution) in self.substitutions.subs.iter()
		{
			match substitution
			{
				SubType::Offset(ArbSymbol(sym)) =>
				{
					// Extract offset value
					let split =
						tokens[*idx].split_at(tokens[*idx].find(",").unwrap_or(tokens[*idx].len()));

					// Add separators after symbol
					let mut replacement = sym.clone();
					replacement.push_str(split.1);
					// replace offset with symbol
					tokens[*idx] = replacement;
				},
				SubType::Ref(symbols) =>
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
						symbols.iter().for_each(|sym_opt| {
							replacement.push_str("=>");
							if let Some(sym) = sym_opt
							{
								replacement.push_str(sym.0.as_str());
							}
							else
							{
								replacement.push('|');
							}
						});
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

		let symbol_addresses = self.substitutions.symbol_addrs.clone();
		(assembly, move |resolve| {
			match resolve
			{
				Resolve::DistanceCurrent(sym) | Resolve::Address(sym) =>
				{
					symbol_addresses
						.get(sym)
						.cloned()
						.map(|addr| addr as i32)
						.ok_or(sym)
				},
				Resolve::Distance(sym1, sym2) =>
				{
					symbol_addresses
						.get(sym2)
						.ok_or(sym2)
						.and_then(|sym2_addr| {
							symbol_addresses
								.get(sym1)
								.ok_or(sym1)
								.and_then(|sym1_addr| Ok((sym2_addr - sym1_addr) as i32))
						})
				},
			}
		})
	}
}
impl<I: ArbInstruction> Arbitrary for AssemblyInstruction<I>
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		let instruction = I::arbitrary(g).extract();
		let substitutions = OperandSubstitutions::arbitrary_from(g, &instruction);

		Self {
			instruction,
			substitutions,
			phantom: PhantomData,
		}
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		let mut result = Vec::new();

		// Shrink substitutions
		for (idx, sub) in &self.substitutions.subs
		{
			let mut substitutions = self.substitutions.subs.clone();
			substitutions.remove(idx);

			match sub
			{
				SubType::Offset(sym) =>
				{
					// Shrink by shrinking the offset in the instruction
					let offset = *get_offset_value(&self.instruction, *idx);
					offset.shrink().for_each(|shrunk_offset| {
						let mut instr_clone = self.instruction.clone();
						*get_offset_value_mut(&mut instr_clone, *idx) = shrunk_offset;

						let mut subs = substitutions.clone();
						subs.insert(*idx, SubType::Offset(sym.clone()));
						let mut substitutions = self.substitutions.clone();
						substitutions.subs = subs;
						*substitutions.symbol_addrs.get_mut(&sym.0).unwrap() =
							OperandSubstitutions::instruction_offset_address(&instr_clone, *idx);

						result.push(Self {
							instruction: instr_clone,
							substitutions,
							phantom: PhantomData,
						});
					});
				},
				SubType::Ref(refs) =>
				{
					if refs.len() > 0
					{
						// Shrink by shrinking the last link offset
						let last_is_offset =
							refs.iter().filter(|sym| sym.is_some()).count() % 2 != 0;
						if last_is_offset
						{
							let last_sym = refs.last().as_ref().unwrap().as_ref().unwrap();
							let last_address = self.substitutions.address_of(last_sym);

							let previous_address = refs
								.iter()
								.rev()
								.skip(1)
								.find(|sym| sym.is_some())
								.map_or(0, |sym| {
									self.substitutions.address_of(sym.as_ref().unwrap())
								});
							let offset = ((last_address - previous_address) / 2) - 1;
							offset.shrink().for_each(|o| {
								let mut clone = self.clone();
								clone
									.substitutions
									.change_address_of(&last_sym, previous_address + ((o + 1) * 2));

								*get_reference_value_mut(&mut clone.instruction, *idx) -=
									(offset - o) as i32;

								result.push(clone);
							});
						}

						// shrink by removing a reference link
						// Only remove last symbol if value is zero
						let value_zero = references(&self.instruction)
							.find(|(i, _)| i == idx)
							.unwrap()
							.1 == 0;
						if value_zero && refs.len() > 1
						{
							let mut instr_clone = self.instruction.clone();
							let mut substitutions_clone = self.substitutions.clone();
							let mut refs_clone = refs.clone();
							if refs.len() >= 2
								&& refs.get(refs.len() - 2).map_or(false, Option::is_none)
							{
								// Second to last is call argument flag, remove it
								assert!(refs_clone.remove(refs.len() - 2).is_none());
								// Increase the last link's address to compensate
								let last_sym =
									refs_clone.last().as_ref().unwrap().as_ref().unwrap();
								substitutions_clone.change_address_of(
									last_sym,
									self.substitutions.address_of(last_sym),
								);
							}
							else
							{
								let removed_sym = refs_clone.pop().unwrap().unwrap();
								let removed_address = self.substitutions.address_of(&removed_sym);

								if last_is_offset
								{
									let previous_address = refs_clone.last().map_or(0, |sym| {
										self.substitutions.address_of(sym.as_ref().unwrap())
									});
									*get_reference_value_mut(&mut instr_clone, *idx) -=
										((removed_address - previous_address) / 2) as i32;
								}
							}
							let mut subs = substitutions.clone();
							subs.insert(*idx, SubType::Ref(refs.clone()));
							substitutions_clone.subs = subs;
							result.push(Self {
								instruction: instr_clone,
								substitutions: substitutions_clone,
								phantom: PhantomData,
							});
						}
					}
				},
			}

			// Shrink by shrinking a symbol
			match sub
			{
				SubType::Offset(sym) =>
				{
					sym.shrink()
						.filter(|s| !self.substitutions.uses_symbol(&s))
						.for_each(|shrunk_sym| {
							let mut clone = self.clone();
							clone
								.substitutions
								.subs
								.insert(*idx, SubType::Offset(shrunk_sym.clone()));
							clone
								.substitutions
								.symbol_addrs
								.insert(shrunk_sym.0, self.substitutions.address_of(sym));
							result.push(clone);
						})
				},
				SubType::Ref(refs) =>
				{
					refs.iter()
						.filter_map(|link| link.as_ref())
						.flat_map(|sym| sym.shrink().map(move |s| (sym, s)))
						.filter(|(_, s)| !self.substitutions.uses_symbol(&s))
						.for_each(|(original, shrunk_sym)| {
							let mut clone = self.clone();
							let mut ref_clone = SubType::Ref(refs.clone());
							ref_clone.replace_uses(original, shrunk_sym.clone());
							clone.substitutions.subs.insert(*idx, ref_clone);
							clone
								.substitutions
								.symbol_addrs
								.insert(shrunk_sym.0, self.substitutions.address_of(original));
							result.push(clone);
						})
				},
			}

			// Shrink by removing the substitution
			let mut clone = self.clone();
			clone.substitutions.subs.remove(idx);
			result.push(clone);
		}

		// Removed any unused address maps
		result
			.iter_mut()
			.for_each(|shrunk| shrunk.substitutions.clean_addrs());

		// Shrink by shrinking unsubstituted operands
		for idx in
			offset_index(&self.instruction).filter(|idx| !self.substitutions.subs.contains_key(idx))
		{
			let offset = *get_offset_value(&self.instruction, idx);
			offset.shrink().for_each(|new_off| {
				let mut clone = self.clone();
				*get_offset_value_mut(&mut clone.instruction, idx) = new_off;
				result.push(clone);
			});
		}
		for (idx, value) in references(&self.instruction)
			.filter(|(idx, _)| !self.substitutions.subs.contains_key(idx))
		{
			value.shrink().for_each(|new_value| {
				let mut clone = self.clone();
				*get_reference_value_mut(&mut clone.instruction, idx) = new_value;
				result.push(clone);
			});
		}

		Box::new(result.into_iter())
	}
}
