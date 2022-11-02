use crate::arbitrary::SeparatorType;
use quickcheck::TestResult;
use scry_isa::{
	arbitrary::{ArbReference, ArbSymbol, AssemblyInstruction, OperandSubstitution},
	Instruction, Parser, Resolve,
};
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
		match Instruction::parse(buffer.split_ascii_whitespace(), |_: Resolve| unreachable!())
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

/// Tests that any valid assembly instruction can be parsed to produce the right
/// instruction
#[quickcheck]
fn parse_assembly(assembly: AssemblyInstruction) -> bool
{
	let (tokens, resolver) = assembly.tokens_and_resolver();
	Instruction::parse(tokens.split_ascii_whitespace(), resolver)
		.map_or(false, |(parsed_instr, ..)| {
			assembly.instruction == parsed_instr
		})
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

	Instruction::parse(tokens.clone(), |resolve: Resolve| {
		if let Resolve::Distance(start, _) = resolve
		{
			injected_symbol.set(start.contains(inject))
		}
		match resolve
		{
			Resolve::Address(sym) | Resolve::DistanceCurrent(sym) | Resolve::Distance(_, sym) =>
			{
				injected_symbol.set(injected_symbol.get() || sym.contains(inject))
			},
		}
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
						// We allow the start_idx to be equal to the length of the token,
						// so that the error message can indicate an error for missing characters
						// that were expected in the same token.
						&& err.start_idx <=tokens.clone().nth(err.start_token).unwrap().len()
						&& err.end_idx <= tokens.clone().nth(err.end_token).unwrap().len(),
				)
			}
		},
		|_| TestResult::discard(),
	)
}

/// Tests that the number of tokens and bytes consumed by parsing is exactly
/// equal to the tokens in the instruction.
/// I.e. ensures that tokens after the instruction are ignored.
#[quickcheck]
fn consumes_only_instruction_tokens(assembly: AssemblyInstruction, extra: String) -> TestResult
{
	let (tokens, resolver) = assembly.tokens_and_resolver();

	let instr_tokens: Vec<_> = tokens.split_ascii_whitespace().collect();
	let extra_tokens: Vec<_> = extra.split_ascii_whitespace().collect();

	let chained = instr_tokens.iter().cloned().chain(extra_tokens.into_iter());

	match assembly.substitutions.last()
	{
		Some((_, OperandSubstitution::Ref(ArbReference(vec))))
			if vec.len() == 0
				&& extra
					.trim_start()
					.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_' || c == '.') =>
		{
			// This will result in valid assembly, e.g. if extra is "x" or "0",
			// the instruction will end on "=>x" or "=>0", which is valid.
			return TestResult::discard();
		},
		_ => (),
	}

	let (_, consumed) = Instruction::parse(chained, resolver).unwrap();

	if consumed.tokens == (instr_tokens.len() - 1)
	{
		if consumed.chars != instr_tokens.last().unwrap().len()
		{
			TestResult::error(format!(
				"Unexpected number of characters consumed (actual != expected): {} != {}",
				consumed.chars,
				instr_tokens.last().unwrap().len()
			))
		}
		else
		{
			TestResult::passed()
		}
	}
	else
	{
		TestResult::error(format!(
			"Unexpected number of tokens consumed (actual != expected): {} != {}",
			consumed.tokens,
			instr_tokens.len() - 1
		))
	}
}

/// Tests that all possible separator combinations are supported for any
/// instruction with separators.
#[quickcheck]
fn different_separator_tokenization(
	assembly: AssemblyInstruction,
	t1: SeparatorType,
	t_rest: Vec<SeparatorType>,
) -> TestResult
{
	const SEPARATORS: &[&'static str] = &["=>", "+", ","];

	let (tokens, resolver) = assembly.tokens_and_resolver();

	// We make an infinite iterator producing separator types for use in the
	// following loop. We do this to ensure some variety to the types each match
	// block gets.
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
			Instruction::parse(edited_assembly.split_ascii_whitespace(), resolver).is_ok(),
		)
	}
	else
	{
		TestResult::discard()
	}
}

/// Tests that if encounters an identifier that isn't an instruction, but does
/// start with the mnemonic of an instruction, a correct error is thrown
#[quickcheck]
fn error_on_mnemonic_prefix(
	assembly: AssemblyInstruction,
	ident_post: ArbSymbol,
	rest: String,
) -> bool
{
	// First get a mnemonic
	let mut test_string = assembly
		.tokens_and_resolver()
		.0
		.split(' ')
		.next()
		.unwrap()
		.to_string();

	// then add a postfix, such that it becomes a symbol
	test_string.push_str(ident_post.0.as_str());

	// Then add rest of string
	test_string.push_str(rest.as_str());

	// Try to parse, and ensure we et an error
	Instruction::parse(test_string.split_ascii_whitespace(), |_: Resolve| 0).is_err()
}
