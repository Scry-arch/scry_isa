use quickcheck::{empty_shrinker, Arbitrary, Gen, TestResult};
use rand::{seq::SliceRandom, Rng};
use scry_isa::{Instruction, Parser};
use std::cell::Cell;

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
		match Instruction::parse(buffer.split(" "), &|_, _| unreachable!())
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
			Err(idx) =>
			{
				println!(
					"Failed to parse instruction.\nText: '{}'\nError Index: {}",
					buffer, idx
				);
				false
			},
		}
	}
}

/// Tests that the number of tokens and bytes consumed by parsing is exactly
/// equal to the tokens in the instruction.
/// I.e. ensures that tokens after the instruction are ignored.
#[quickcheck]
fn consumes_only_instruction_tokens(instr: Instruction, extra: String) -> bool
{
	let mut buffer = String::new();
	Instruction::print(&instr, &mut buffer).unwrap();

	let instr_tokens: Vec<_> = buffer.split(" ").collect();
	let extra_tokens: Vec<_> = extra.split(" ").collect();

	let (_, consumed, bytes) = Instruction::parse(
		instr_tokens.iter().cloned().chain(extra_tokens.into_iter()),
		&|_, _| unreachable!(),
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
fn different_separators(
	instr: Instruction,
	t1: SeparatorType,
	t_rest: Vec<SeparatorType>,
) -> quickcheck::TestResult
{
	const SEPARATORS: &[&'static str] = &["=>", "+", ","];

	let mut buffer = String::new();
	Instruction::print(&instr, &mut buffer).unwrap();

	// We make an infinite iterator producing comma types for use in the following
	// loop. We do this to ensure some variety to the types each match block gets.
	let mut separator_types = Some(t1).into_iter().chain(t_rest.into_iter()).cycle();

	if let Some(_) = SEPARATORS.iter().find(|sep| buffer.contains(*sep))
	{
		let mut edited_assembly = String::new();
		let mut rest = buffer.as_str();

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
			Instruction::parse(
				edited_assembly.split(" ").filter(|t| !t.is_empty()),
				&|_, _| unreachable!(),
			)
			.is_ok(),
		)
	}
	else
	{
		TestResult::discard()
	}
}

/// Tests that if parsing fails because of bad syntax, the reported index is
/// always within the tokens of the instruction
#[quickcheck]
fn error_index_only_in_instruction(
	instr: Instruction,
	inject: char,
	mut inject_idx: usize,
	postfix: String,
) -> TestResult
{
	let mut buffer = String::new();
	Instruction::print(&instr, &mut buffer).unwrap();

	// We also count commas because they can be on their own, but the default
	// print puts at adjacent to teh previous token, which means space counting
	// doesn't count the comma.
	let instr_token_count = buffer.split(" ").count() + (buffer.split(",").count() - 1);

	// Inject string at next char boundary
	inject_idx = inject_idx % buffer.as_str().len();
	while !buffer.as_str().is_char_boundary(inject_idx)
	{
		inject_idx += 1;
	}
	buffer.insert(inject_idx, inject);

	buffer.push_str(postfix.as_str());
	let injected_symbol = Cell::new(false);
	Instruction::parse(buffer.split(" ").into_iter(), &|start, end| {
		if let Some(start) = start
		{
			injected_symbol.set(start.contains(inject))
		}
		injected_symbol.set(injected_symbol.get() || end.contains(inject));
		0
	})
	.map_or_else(
		|idx| {
			if injected_symbol.get()
			{
				TestResult::discard()
			}
			else
			{
				TestResult::from_bool(idx < instr_token_count)
			}
		},
		|_| TestResult::discard(),
	)
}

#[derive(Clone, Debug)]
struct Symbol(String);
impl Arbitrary for Symbol
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

		Box::new(
			result
				.into_iter()
				.filter(|Symbol(s)| !s.chars().nth(0).unwrap().is_numeric()),
		)
	}
}
#[derive(Clone, Debug)]
struct OffsetInstruction(Instruction);
impl Arbitrary for OffsetInstruction
{
	fn arbitrary<G: Gen>(g: &mut G) -> Self
	{
		use Instruction::*;
		loop
		{
			let instruction = Instruction::arbitrary(g);
			match &instruction
			{
				Jump(..) | Call(..) => return Self(instruction),
				_ => (),
			}
		}
	}
}
impl OffsetInstruction
{
	fn offset_index(&self) -> impl Iterator<Item = usize>
	{
		use Instruction::*;
		match self.0
		{
			Jump(..) => [1, 2].iter(),
			Call(..) => [1].iter(),
			_ => panic!("Instruction doesn't have offset operand."),
		}
		.cloned()
	}
}

/// Tests that instructions that take address offset operands accept any symbol
/// instead of integer offsets.
#[quickcheck]
fn accepts_symbol_offsets(instr: OffsetInstruction, Symbol(sym): Symbol, skip: usize) -> bool
{
	let mut buffer = String::new();
	Instruction::print(&instr.0, &mut buffer).unwrap();
	let mut tokens: Vec<_> = buffer.split(" ").collect();

	// Extract offset value
	let offset_index = instr
		.offset_index()
		.skip(skip % instr.offset_index().count())
		.next()
		.unwrap();
	let split = tokens[offset_index].split_at(
		tokens[offset_index]
			.find(",")
			.unwrap_or(tokens[offset_index].len()),
	);
	let offset_value: i32 = split.0.parse().unwrap();

	// replace offset with symbol
	let mut replacement = String::from(sym.as_str());
	replacement.push_str(split.1);
	tokens[offset_index] = replacement.as_str();

	Instruction::parse(tokens.into_iter(), &|_, _| offset_value).is_ok()
}

#[derive(Clone, Debug)]
struct ReferenceInstruction(Instruction);
impl Arbitrary for ReferenceInstruction
{
	fn arbitrary<G: Gen>(g: &mut G) -> Self
	{
		use Instruction::*;
		loop
		{
			let instruction = Instruction::arbitrary(g);
			match &instruction
			{
				Echo(..) | EchoLong(..) | Alu(..) | Alu2(..) => return Self(instruction),
				_ => (),
			}
		}
	}
}
impl ReferenceInstruction
{
	fn reference_index(&self) -> impl Iterator<Item = usize>
	{
		use Instruction::*;
		match self.0
		{
			Echo(..) => [1, 2].iter(),
			EchoLong(..) | Alu(..) => [1].iter(),
			Alu2(..) => [2].iter(),
			_ => panic!("Instruction doesn't have reference operand."),
		}
		.cloned()
	}
}

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

/// Tests that instructions that take output target operands accept any symbol
/// reference chain instead of integer reference.
#[quickcheck]
fn accepts_symbol_references(
	instr: ReferenceInstruction,
	Reference(symbols): Reference,
	skip: usize,
) -> bool
{
	let mut buffer = String::new();
	Instruction::print(&instr.0, &mut buffer).unwrap();
	let mut tokens: Vec<_> = buffer.split(" ").collect();

	// Extract reference value
	let reference_index = instr
		.reference_index()
		.skip(skip % instr.reference_index().count())
		.next()
		.unwrap();
	let split = tokens[reference_index]
		// remove the preceding '=>'
		.split_at(2).1
		// potentially remove ',' at end
		.split_at(tokens[reference_index].find(",").unwrap_or(tokens[reference_index].len())-2);

	let reference_value: i32 = split.0.parse().unwrap();

	// replace reference with symbols
	let mut replacement = String::new();
	for i in 0..std::cmp::min(reference_value + 1, symbols.len() as i32)
	{
		replacement.push_str("=>");
		replacement.push_str(symbols[i as usize].0.as_str());
	}
	replacement.push_str(split.1);
	tokens[reference_index] = replacement.as_str();

	Instruction::parse(tokens.into_iter(), &|_, _| 2).is_ok()
}
