use duplicate::duplicate_item;
use quickcheck::{Arbitrary, Gen, TestResult};
use scry_isa::{
	arbitrary::{ArbSymbol, AssemblyInstruction, OperandSubstitutions, SubType},
	AluVariant, Bits, Instruction, ParseError, ParseErrorType, Parser, ReferenceNode, Resolve,
};
use std::{cell::Cell, collections::HashMap, convert::TryInto, marker::PhantomData};

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

/// Takes the given assembly instruction and tests that it is assembled to the
/// correct instruction.
fn test_parse_assembly(assembly: AssemblyInstruction<Instruction>) -> TestResult
{
	let (tokens, resolver) = assembly.tokens_and_resolver();
	Instruction::parse(tokens.split_ascii_whitespace(), resolver).map_or_else(
		|err| TestResult::error(format!("Failed to parse: {:?}", err)),
		|(parsed_instr, ..)| {
			if assembly.instruction == parsed_instr
			{
				TestResult::passed()
			}
			else
			{
				TestResult::error(format!(
					"Unexpected result of parsing (expected != actual): {:?} != {:?}",
					assembly.instruction, parsed_instr
				))
			}
		},
	)
}

/// Tests that any valid assembly instruction can be parsed to produce the right
/// instruction
#[quickcheck]
fn parse_assembly(assembly: AssemblyInstruction) -> TestResult
{
	test_parse_assembly(assembly)
}

/// Tests where the error is reported in "echo =>q=>q2=>q3" if q3 precedes q2
#[test]
fn parse_assembly_error_1()
{
	let assembly = AssemblyInstruction::<Instruction> {
		instruction: Instruction::EchoLong(Bits::try_from(32).unwrap()),
		substitutions: OperandSubstitutions {
			subs: [(
				1,
				SubType::Ref(
					[
						Some(ArbSymbol("q".into())),
						Some(ArbSymbol("q2".into())),
						Some(ArbSymbol("q3".into())),
					]
					.into(),
				),
			)]
			.into(),
			symbol_addrs: [("q".into(), 66), ("q2".into(), 100), ("q3".into(), 50)].into(),
		},
		phantom: Default::default(),
	};

	let (tokens, resolver) = assembly.tokens_and_resolver();
	assert_eq!(
		Instruction::parse(tokens.split_ascii_whitespace(), resolver),
		Err(ParseError {
			start_token: 1,
			start_idx: 0,
			end_token: 1,
			end_idx: 11,
			err_type: ParseErrorType::InvalidReference(
				Some(2),
				vec!(
					ReferenceNode::Symbol("q"),
					ReferenceNode::Symbol("q2"),
					ReferenceNode::Symbol("q3")
				)
			),
		})
	)
}

/// Test specific cases of `parse_assembly`
#[duplicate_item(
	name	instr	subs;

	// Tests assembly can use a reference of just one symbol, e.g. "add =>label"
	[ parse_assembly_single_symbol ]
	[ Instruction::Alu(AluVariant::Add, 5.try_into().unwrap()) ]
	[ 1, vec![Some(("label", 12))] ];

	// Tests assembly can use a reference to the first instruction after a control
	// flow trigger E.g. "Add =>label1=>label2"
	[ parse_assembly_to_jump ]
	[ Instruction::Alu(AluVariant::Add, 12.try_into().unwrap()) ]
	[ 1, vec![
		Some(("label1", 26)),
		Some(("label2", 124))
	]];

	// Tests assembly can use a reference to an offset after a control flow trigger
	// E.g. "sub =>label1=>label2=>label3"
	[ parse_assembly_to_after_jump ]
	[ Instruction::Alu(AluVariant::Sub, 15.try_into().unwrap()) ]
	[ 1, vec![
		Some(("label1", 26)),
		Some(("label2", 124)),
		Some(("label3", 130))
	]];

	// Tests assembly can use a reference with multiple control-flow triggers
	// E.g. "Echo =>0, =>label1=>label2=>label3=>label4=>label5"
	[ parse_assembly_multi_jump ]
	[ Instruction::Echo(false, 0.try_into().unwrap(), 12.try_into().unwrap()) ]
	[ 2, vec![
		Some(("label1", 12)),
		Some(("label2", 560)),
		Some(("label3", 564)),
		Some(("label4", 56)),
		Some(("label5", 66))
	]];

	// Tests assembly can use a reference with a call argument flag
	// E.g. "sub =>|=>label"
	[ parse_assembly_argument_flag ]
	[ Instruction::Alu(AluVariant::Sub, 15.try_into().unwrap()) ]
	[ 1, vec![
		None,
		Some(("label1", 30))
	]];

	// Tests assembly can use a reference with multiple call argument flags
	// E.g. "dup =>|=>|=>label, =>0"
	[ parse_assembly_multiple_argument_flags ]
	[ Instruction::Duplicate(false, 9.try_into().unwrap(), 0.try_into().unwrap()) ]
	[ 1, vec![
		None,
		None,
		Some(("label1", 16))
	]];

	// Tests assembly can use a reference with call argument flags after a jump
	// E.g. "dec =>label1=>label2=>|=>label3"
	[ parse_assembly_argument_flags_after_jump ]
	[ Instruction::Pick(6.try_into().unwrap()) ]
	[ 1, vec![
		Some(("label1", 6)),
		Some(("label2", 456)),
		None,
		Some(("label3", 462)),
	]];

	// Tests assembly long echo
	[ parse_assembly_echo_long ]
	[ Instruction::EchoLong(32.try_into().unwrap()) ]
	[ 1, vec![
		Some(("label1", 66)),
	]];
)]
#[test]
fn name()
{
	let result = test_parse_assembly(AssemblyInstruction {
		instruction: instr,
		substitutions: OperandSubstitutions::from_reference(subs),
		phantom: Default::default(),
	});
	assert!(!result.is_failure(), "{:?}", result);
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
		Ok(0)
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
fn consumes_only_instruction_tokens(assembly: AssemblyInstruction, extra: String) -> TestResult
{
	let (tokens, resolver) = assembly.tokens_and_resolver();

	let instr_tokens: Vec<_> = tokens.split_ascii_whitespace().collect();
	let extra_tokens: Vec<_> = extra.split_ascii_whitespace().collect();
	let extra_start_with_var = extra
		.trim_start()
		.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_' || c == '.');

	let chained = instr_tokens.iter().cloned().chain(extra_tokens.into_iter());

	if let Some((_, SubType::Ref(vec))) = assembly.substitutions.subs.iter().last()
	{
		if vec.len() == 0 && extra_start_with_var
		{
			// This will result in valid assembly, e.g. if extra is "x" or "0",
			// the instruction will end on "=>x" or "=>0", which is valid.
			return TestResult::discard();
		}
	}
	if let Instruction::Request(imm) = assembly.instruction
	{
		if imm.value == 255 && extra_start_with_var
		{
			// Extra might result in valid request assembly that doesn't match
			// the instruction (which has implicit operand) e.g., "req" + "0"
			return TestResult::discard();
		}
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

#[quickcheck]
fn consumes_only_instruction_tokens_prop(assembly: AssemblyInstruction, extra: String)
	-> TestResult
{
	consumes_only_instruction_tokens(assembly, extra)
}

#[test]
fn consumes_only_instruction_tokens_1()
{
	let assembly = AssemblyInstruction {
		instruction: Instruction::Request(255.try_into().unwrap()),
		substitutions: OperandSubstitutions {
			subs: HashMap::new(),
			symbol_addrs: HashMap::new(),
		},
		phantom: PhantomData,
	};
	let result = consumes_only_instruction_tokens(assembly, "0".to_string());
	assert!(!result.is_failure(), "{:?}", result);
}

/// Tests that all possible separator combinations are supported for any
/// instruction with separators.
fn different_separator_tokenization(
	assembly: AssemblyInstruction,
	t1: SeparatorType,
	t_rest: Vec<SeparatorType>,
) -> TestResult
{
	const SEPARATORS: &[&'static str] = &["=>", "+", ",", "|"];

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

#[quickcheck]
fn different_separator_tokenization_prop(
	assembly: AssemblyInstruction,
	t1: SeparatorType,
	t_rest: Vec<SeparatorType>,
) -> TestResult
{
	different_separator_tokenization(assembly, t1, t_rest)
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
	Instruction::parse(test_string.split_ascii_whitespace(), |_: Resolve| Ok(0)).is_err()
}
