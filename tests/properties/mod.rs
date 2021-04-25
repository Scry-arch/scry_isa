use quickcheck::{empty_shrinker, Arbitrary, Gen, TestResult};
use rand::{seq::SliceRandom, Rng};
use scry_isa::{Instruction, Parser};
use std::{cell::Cell, collections::HashMap};

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
enum Symbolized
{
	Offset(Symbol),
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
struct Symbol(String);
impl Arbitrary for Symbol
{
	fn arbitrary<G: Gen>(g: &mut G) -> Self
	{
		const SYMBOL_CHARS: &'static str =
			"-0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_.";

		let size = g.gen_range(1, g.size());
		let mut result = String::new();

		// First character cannot be numeric or '-'
		result.push(
			SYMBOL_CHARS
				.chars()
				.nth(g.gen_range(11, SYMBOL_CHARS.len()))
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

		Box::new(result.into_iter().filter(|Symbol(s)| {
			let c = s.chars().nth(0).unwrap();
			!(c.is_numeric() || c == '-')
		}))
	}
}

/// An output reference e.g. "=>branch=>branch_to=>target"
#[derive(Clone, Debug)]
struct Reference(Vec<Symbol>);
impl Arbitrary for Reference
{
	fn arbitrary<G: Gen>(g: &mut G) -> Self
	{
		let mut result = Vec::<Symbol>::arbitrary(g);
		// Ensure there is at least 1
		result.push(Arbitrary::arbitrary(g));
		Self(result)
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		let mut result: Vec<_> = Vec::new();
		result.extend(self.0.clone().shrink().filter(|v| !v.is_empty()));

		for i in 0..self.0.len()
		{
			result.extend(self.0[i].shrink().map(|sym| {
				let mut copy = self.0.clone();
				copy[i] = sym;
				copy
			}));
		}

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

/// Returns the indices of output reference operands, e.g., 1 in "add =>2"
fn reference_index(instr: &Instruction) -> impl Iterator<Item = usize>
{
	use Instruction::*;
	match instr
	{
		Echo(..) => [1, 2].iter(),
		EchoLong(..) | Alu(..) => [1].iter(),
		Alu2(..) => [2].iter(),
		// We don't use the wildcard match to not forget to add instructions above
		Jump(..) | Call(..) => [].iter(),
	}
	.cloned()
}

/// An instruction in assembly format.
#[derive(Clone, Debug)]
struct AssemblyInstruction(Instruction, Vec<(usize, Symbolized)>);
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
		for idx in reference_index(&instruction)
		{
			// Sometimes keep the integer references
			if g.gen_bool(0.5)
			{
				symbolized.push((idx, Symbolized::Ref(Arbitrary::arbitrary(g))))
			}
		}
		Self(instruction, symbolized)
	}

	fn shrink(&self) -> Box<dyn Iterator<Item = Self>>
	{
		let mut result = Vec::new();

		result.extend(self.0.shrink().map(|instr| Self(instr, self.1.clone())));

		for i in 0..self.1.len()
		{
			// Shrink by removing an element
			let mut symbolized = self.1.clone();
			let removed = symbolized.remove(i);
			result.push(Self(self.0.clone(), symbolized.clone()));

			// Shrink by shrinking an element
			removed.1.shrink().for_each(|sym| {
				let mut symbolized2 = symbolized.clone();
				symbolized2.push((removed.0, sym));
				result.push(Self(self.0.clone(), symbolized2));
			})
		}

		Box::new(result.into_iter())
	}
}
impl AssemblyInstruction
{
	/// Returns the assembly instruction and a resolver for any symbols.
	fn tokens_and_resolver(&self) -> (String, impl Fn(Option<&str>, &str) -> i32)
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
					let offset_value: i32 = split.0.parse().unwrap();

					// replace offset with symbol
					let mut replacement = sym.0.clone();
					symbol_addresses.insert(replacement.clone(), offset_value * 2);

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
					let reference_value: i32 = split.0.parse().unwrap();

					// replace reference with symbols
					let mut replacement = String::new();
					for i in 0..std::cmp::min(reference_value + 1, symbols.len() as i32)
					{
						replacement.push_str("=>");
						replacement.push_str(symbols[i as usize].0.as_str());
						symbol_addresses.insert(symbols[i as usize].0.clone(), (i + 1) * 2);
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

/// Tests that any valid assembly instruction can be parsed.
#[quickcheck]
fn parse_assembly(assembly: AssemblyInstruction) -> bool
{
	let (tokens, resolver) = assembly.tokens_and_resolver();
	Instruction::parse(tokens.split_ascii_whitespace(), &resolver).is_ok()
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
