use quickcheck::{empty_shrinker, Arbitrary, Gen, TestResult};
use rand::{seq::SliceRandom, Rng};
use scry_isa::{Instruction, Parser};
use std::{cell::Cell, collections::HashMap};
use duplicate::duplicate;

/// Tests that if we first print an instruction and then parse the printed text
/// we will get the exact same instruction as we started with.
#[quickcheck]
fn print_then_parse(instr: Instruction) -> bool
{
	let mut buffer = String::new();
	if let Err(err) = Instruction::print(&instr, &mut buffer)
	{
		println!(
			"Failed to print instruction.\n Instruction: [{:?}]\n Error: {}",
			instr, err
		);
		false
	}
	else
	{
		match Instruction::parse(buffer.split_ascii_whitespace(), &|_, _| unreachable!())
		{
			Ok((instr2, ..)) =>
			{
				if instr != instr2
				{
					println!("{:?} => {:?}", instr, instr2);
					false
				}
				else
				{
					true
				}
			},
			Err(err) =>
			{
				println!(
					"Failed to parse instruction.\nText: '{}'\nError: {:?}",
					buffer, err
				);
				false
			},
		}
	}
}

/// Tests that if parsing fails because of bad syntax, the reported span is
/// always within the tokens of the instruction
#[quickcheck]
fn error_only_in_instruction(
	instr: Instruction,
	inject: char,
	inject_rest: String,
	mut inject_idx: usize,
	postfix: String,
) -> TestResult
{
	let mut buffer = String::new();
	Instruction::print(&instr, &mut buffer).unwrap();

	// Inject string at next char boundary
	inject_idx = inject_idx % buffer.as_str().len();
	while !buffer.as_str().is_char_boundary(inject_idx)
	{
		inject_idx += 1;
	}
	// Inject last chars first so we don't have to change the index
	buffer.insert_str(inject_idx, inject_rest.as_str());
	// Then insert the first char before the previously inserted
	buffer.insert(inject_idx, inject);
	let instr_token_count = buffer.split_ascii_whitespace().count();

	buffer.push_str(postfix.as_str());
	let injected_symbol = Cell::new(false);
	let tokens = buffer.split_ascii_whitespace().into_iter();
	Instruction::parse(tokens.clone(), &|start, end| {
		if let Some(start) = start
		{
			injected_symbol.set(start.contains(inject))
		}
		injected_symbol.set(injected_symbol.get() || end.contains(inject));
		0
	})
	.map_or_else(
		|err| {
			if injected_symbol.get()
			{
				TestResult::discard()
			}
			else
			{
				TestResult::from_bool(
					err.start_token < instr_token_count
						&& err.end_token < instr_token_count
						&& err.start_idx < tokens.clone().nth(err.start_token).unwrap().len()
						&& err.end_idx <= tokens.clone().nth(err.end_token).unwrap().len(),
				)
			}
		},
		|_| TestResult::discard(),
	)
}

#[derive(Clone, Debug)]
pub(crate) enum Symbolized
{
	Offset(ArbSymbol),
	Ref(Reference),
}
impl Arbitrary for Symbolized
{
	fn arbitrary<G: Gen>(_: &mut G) -> Self
	{
		unimplemented!()
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		use Symbolized::*;
		match self
		{
			Offset(s) => Box::new(s.shrink().map(|s| Offset(s))),
			Ref(s) => Box::new(s.shrink().map(|s| Ref(s))),
		}
	}
}

/// An assembly symbol
#[derive(Clone, Debug)]
pub(crate) struct ArbSymbol(pub String);
impl Arbitrary for ArbSymbol
{
	fn arbitrary<G: Gen>(g: &mut G) -> Self
	{
		const SYMBOL_CHARS: &'static str =
			"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ-_.";

		let size = g.gen_range(1, g.size());
		let mut result = String::new();

		// First character cannot be numeric
		result.push(
			SYMBOL_CHARS
				.chars()
				.nth(g.gen_range(10, SYMBOL_CHARS.len()))
				.unwrap(),
		);

		for _ in 1..size
		{
			result.push(
				SYMBOL_CHARS
					.chars()
					.nth(g.gen_range(0, SYMBOL_CHARS.len()))
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

/// An output reference e.g. "=>branch=>branch_to=>target"
#[derive(Clone, Debug)]
pub(crate) struct Reference(pub Vec<(ArbSymbol, i32)>);
impl Arbitrary for Reference
{
	fn arbitrary<G: Gen>(g: &mut G) -> Self
	{
		let mut result = Vec::<ArbSymbol>::arbitrary(g);
		// Ensure there is at least 1
		result.push(Arbitrary::arbitrary(g));
		Self(result.into_iter().enumerate().map(|(i, s)| (s, ((i+1)*2) as i32)).collect::<Vec<_>>())
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		let mut result: Vec<_> = Vec::new();
		
		// Shrink by shrinking symbol names
		result.extend(self.0.iter().enumerate()
			.flat_map(|(i, (sym, address))| sym.shrink().map(move|sym| {
				let mut clone = self.0.clone();
				clone[i] = (sym, *address);
				clone
			})));
		
		Box::new(result.into_iter().map(|vec| Self(vec)))
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
		Echo(..) | EchoLong(..) | Alu(..) | Alu2(..) => [].iter(),
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
		_ => panic!("Invalid reference index '{}' for instruction '{:?}'", idx, instruction_clone),
	}
}

/// Returns the indices of output reference operands, e.g., 1 in "add =>2"
/// and their integer value in the instruction
fn references(instr: &Instruction) -> impl Iterator<Item=(usize, i32)>
{
	use Instruction::*;
	match instr
	{
		Echo(first, second,_) => vec![(1, first.value()), (2, second.value())],
		EchoLong(b) => vec![(1, b.value())],
		Alu(_, b) => vec![(1, b.value())],
		Alu2(_,_,b) => vec![(2, b.value())],
		// We don't use the wildcard match to not forget to add instructions above
		Jump(..) | Call(..) => vec![],
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
		Echo(first, _,_) if idx == 1 => ref_type([first.value]),
		Echo(_, second,_) if idx == 2 => ref_type([second.value]),
		EchoLong(b) if idx == 1 => ref_type([b.value]),
		Alu(_, b) if idx == 1 => ref_type([b.value]),
		Alu2(_,_,b) if idx == 2 => ref_type([b.value]),
		_ => panic!("Invalid reference index '{}' for instruction '{:?}'", idx, instruction_clone),
	}
}

/// An instruction in assembly format.
#[derive(Clone, Debug)]
pub(crate) struct AssemblyInstruction(pub Instruction, pub Vec<(usize, Symbolized)>);
impl Arbitrary for AssemblyInstruction
{
	fn arbitrary<G: Gen>(g: &mut G) -> Self
	{
		let instruction = Instruction::arbitrary(g);
		let mut symbolized = Vec::new();
		// Replace integer offsets with symbols
		for idx in offset_index(&instruction)
		{
			// Sometimes keep the integer offset
			if g.gen_bool(0.5)
			{
				symbolized.push((idx, Symbolized::Offset(Arbitrary::arbitrary(g))))
			}
		}

		// Replace integer output references with symbols
		for (idx, value) in references(&instruction)
		{
			// Sometimes keep the integer references
			if g.gen_bool(0.5)
			{
				if value == 0  && g.gen_bool(0.5) {
					// Sometimes omit the symbol for referencing the next instruction
					// i.e. "=>0" becomes "=>"
					symbolized.push((idx, Symbolized::Ref(Reference(vec!()))));
				} else {
					let mut result_refs = Vec::new();
					let first_offset = g.gen_range(0, value + 1);
					result_refs.push((Arbitrary::arbitrary(g), (1+ first_offset)*2));
					
					let mut value_left = value - first_offset;
					let mut last_address: i32 = result_refs[0].1 ;
					let mut next_branch_to = true;
					
					while value_left > 0 {
						if next_branch_to {
							last_address = g.gen_range(i32::MIN / 2, (i32::MAX / 2) - value_left) * 2;
						} else {
							let next_offset = g.gen_range(1, 1 + value_left);
							last_address += next_offset*2;
							value_left -= next_offset;
						}
						result_refs.push((Arbitrary::arbitrary(g), last_address));
						next_branch_to = !next_branch_to;
					}
					symbolized.push((idx, Symbolized::Ref(Reference(result_refs))))
				}
			}
		}
		Self(instruction, symbolized)
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		let mut result = Vec::new();

		for i in 0..self.1.len()
		{
			let mut symbolized = self.1.clone();
			let (removed_idx, removed_symbolized) = symbolized.remove(i);
			
			//shrink by removing a substitution
			result.push(Self(self.0.clone(), symbolized.clone()));
			
			match removed_symbolized {
				Symbolized::Offset(ref sym) => {
					// Shrink by shrinking the offset
					let mut tmp_clone = self.0.clone();
					let offset = *get_offset_value(&mut tmp_clone, removed_idx);
					offset.shrink().for_each(|o| {
						let mut instr_clone = self.0.clone();
						*get_offset_value_mut(&mut instr_clone, removed_idx) = o;
						
						let mut symbolized2 = symbolized.clone();
						symbolized2.push((removed_idx, Symbolized::Offset(sym.clone())));
						result.push(Self(instr_clone, symbolized2));
					});
				}
				Symbolized::Ref(Reference(ref refs)) => {
					if refs.len() > 0 {
						// Shrink by shrinking the last link offset
						if refs.len() % 2 != 0 {
							// The last link is an offset
							let mut refs_clone = refs.clone();
							let (removed_sym, removed_address) = refs_clone.pop().unwrap();
							
							let previous_address = refs_clone.last().map_or(0, |(_, a)| *a);
							
							let offset = ((removed_address - previous_address)/2)-1;
							offset.shrink().for_each(|o| {
								let mut instr_clone = self.0.clone();
								let mut refs_clone = refs_clone.clone();
								
								refs_clone.push((removed_sym.clone(), previous_address+2+(o*2)));
								*get_reference_value_mut(&mut instr_clone, removed_idx) -=
									offset-o;
								
								let mut symbolized2 = symbolized.clone();
								symbolized2.push((removed_idx, Symbolized::Ref(Reference(refs_clone))));
								result.push(Self(instr_clone, symbolized2));
							});
						}
						
						// shrink by removing a reference link
						let mut instr_clone = self.0.clone();
						let mut refs_clone = refs.clone();
						let (_, removed_address) = refs_clone.pop().unwrap();
						
						if refs.len() % 2 != 0 {
							// The last link is an offset
							let previous_address = refs_clone.last().map_or(0, |(_, a)| *a);
							*get_reference_value_mut(&mut instr_clone, removed_idx) -=
								((removed_address-previous_address)/2)
								// If removing the last link, need to
								// simulate target is address 2
								- (refs.len() == 1) as i32;
						}
						let mut symbolized2 = symbolized.clone();
						symbolized2.push((removed_idx, Symbolized::Ref(Reference(refs_clone))));
						result.push(Self(instr_clone, symbolized2));
					}
				}
			}
			
			// Shrink by shrinking a symbol (from the removed offset/reference)
			removed_symbolized.shrink().for_each(|sym| {
				let mut symbolized2 = symbolized.clone();
				symbolized2.push((removed_idx, sym));
				result.push(Self(self.0.clone(), symbolized2));
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

		for (idx, symbolized) in self.1.iter()
		{
			match symbolized
			{
				Symbolized::Offset(sym) =>
				{
					// Extract offset value
					let split =
						tokens[*idx].split_at(tokens[*idx].find(",").unwrap_or(tokens[*idx].len()));
					let offset_value = *get_offset_value(&self.0, *idx);

					// replace offset with symbol
					let mut replacement = sym.0.clone();
					let symbol_address = match self.0 {
						Instruction::Jump(_,second) if *idx==1 && offset_value>0 => {
							(second.value()+1+offset_value)*2
						},
						_ => (offset_value + ((offset_value>=0) as i32)) * 2,
					};
					symbol_addresses.insert(replacement.clone(), symbol_address);

					// Add separators after offset value
					replacement.push_str(split.1);
					tokens[*idx] = replacement;
				},
				Symbolized::Ref(Reference(symbols)) =>
				{
					// Extract reference value
					let split = tokens[*idx]
						// remove the preceding '=>'
						.split_at(2).1
						// potentially remove ',' at end
						.split_at(tokens[*idx].find(",").unwrap_or(tokens[*idx].len())-2);

					// replace reference with symbols
					let mut replacement = String::new();
					if symbols.len() == 0 {
						replacement.push_str("=>");
					} else {
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

/// Tests that any valid assembly instruction can be parsed to produce the right
/// instruction
#[quickcheck]
fn parse_assembly(assembly: AssemblyInstruction) -> bool
{
	let (tokens, resolver) = assembly.tokens_and_resolver();
	Instruction::parse(tokens.clone().split_ascii_whitespace(), &resolver).map_or(false, |(parsed_instr,..)|
		assembly.0 == parsed_instr
	)
}

/// Tests that the number of tokens and bytes consumed by parsing is exactly
/// equal to the tokens in the instruction.
/// I.e. ensures that tokens after the instruction are ignored.
#[quickcheck]
fn consumes_only_instruction_tokens(assembly: AssemblyInstruction, extra: String) -> bool
{
	let (tokens, resolver) = assembly.tokens_and_resolver();

	let instr_tokens: Vec<_> = tokens.split_ascii_whitespace().collect();
	let extra_tokens: Vec<_> = extra.split_ascii_whitespace().collect();

	let (_, consumed, bytes) = Instruction::parse(
		instr_tokens.iter().cloned().chain(extra_tokens.into_iter()),
		&resolver,
	)
	.unwrap();

	(consumed == (instr_tokens.len() - 1)) && (bytes == instr_tokens.last().unwrap().len())
}

/// Represents the different ways separator character sequences (",", "=>",
/// etc.) can be in separate tokens
#[derive(Clone, Copy, Debug)]
enum SeparatorType
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
	fn arbitrary<G: Gen>(g: &mut G) -> Self
	{
		use SeparatorType::*;
		*[AtEnd, AtStart, InMiddle, Alone].choose(g).unwrap()
	}
}

/// Tests that all possible separator combinations are supported for any
/// instruction with separators.
#[quickcheck]
fn different_separator_tokenization(
	assembly: AssemblyInstruction,
	t1: SeparatorType,
	t_rest: Vec<SeparatorType>,
) -> quickcheck::TestResult
{
	const SEPARATORS: &[&'static str] = &["=>", "+", ","];

	let (tokens, resolver) = assembly.tokens_and_resolver();

	// We make an infinite iterator producing comma types for use in the following
	// loop. We do this to ensure some variety to the types each match block gets.
	let mut separator_types = Some(t1).into_iter().chain(t_rest.into_iter()).cycle();

	if let Some(_) = SEPARATORS.iter().find(|sep| tokens.contains(*sep))
	{
		let mut edited_assembly = String::new();
		let mut rest = tokens.as_str();

		while let Some((idx, separator)) = SEPARATORS
			.iter()
			.find_map(|sep| rest.find(sep).map(|idx| (idx, sep)))
		{
			let (split1, split2) = rest.split_at(idx);

			let next_separator_type = separator_types.next().unwrap();
			match next_separator_type
			{
				// Remove any spaces before the separator to ensure it stays in the same token as
				// preceding text
				SeparatorType::AtEnd | SeparatorType::InMiddle =>
				{
					edited_assembly.push_str(split1.trim_end())
				},
				// Add a space before separator to ensure it is separated into a different token
				// Than preceding text
				_ =>
				{
					edited_assembly.push_str(split1);
					edited_assembly.push(' ');
				},
			}
			edited_assembly.push_str(separator);
			let after_separator = split2.split_at(separator.len()).1;
			rest = match next_separator_type
			{
				// Remove any spaces after the separator to ensure it stays in the same token as
				// succeeding text
				SeparatorType::AtStart | SeparatorType::InMiddle => after_separator.trim_start(),
				// Add a space after separator to ensure it is separated into a different token
				// than succeeding text
				_ =>
				{
					edited_assembly.push(' ');
					after_separator
				},
			};
		}
		edited_assembly.push_str(rest);

		TestResult::from_bool(
			Instruction::parse(edited_assembly.split_ascii_whitespace(), &resolver).is_ok(),
		)
	}
	else
	{
		TestResult::discard()
	}
}
