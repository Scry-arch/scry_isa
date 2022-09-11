use scry_isa::{Instruction, ParseError, Parser};
use std::borrow::Borrow;

/// Parses the given string into an instruction.
fn parse_assembly<'a, F, B>(asm: &'a str, f: B) -> Result<Instruction, ParseError<'a>>
where
	B: Borrow<F>,
	F: Fn(Option<&str>, &str) -> i32,
{
	let tokens: Vec<_> = asm.split_ascii_whitespace().collect();
	Instruction::parse(tokens.iter().cloned(), f).map(|(instr, ..)| instr)
}

/// Tests that the given source assembly string parses (using the given
/// resolver) into an instruction that then prints into the expected assembly
/// string.
fn test_case<'a, F, B>(source_asm: &str, expected_asm: &str, resolver: B, expected_bin: Option<u16>)
where
	B: Borrow<F>,
	F: Fn(Option<&str>, &str) -> i32,
{
	let instr = parse_assembly(source_asm, resolver)
		.unwrap_or_else(|err| panic!("Failed to parse '{}': '{:?}'", source_asm, err));
	let mut buff = String::new();
	Instruction::print(&instr, &mut buff).unwrap();
	assert_eq!(buff, expected_asm, "From: \"{}\"", source_asm);

	// Check that if we encode the instruction, we decode it to the same instruction
	let encoded = instr.encode();
	let decoded = Instruction::decode(encoded);
	assert_eq!(instr, decoded, "Error in encode/decode.");

	if let Some(expected_bin) = expected_bin
	{
		let encoded = instr.encode();
		assert_eq!(encoded, expected_bin, "From: \"{}\"", source_asm);
		assert_eq!(
			instr,
			Instruction::decode(expected_bin),
			"From: \"{}\"",
			source_asm
		);
	}
}

/// Tests the parsing of specific assembly instruction.
///
/// An instruction is given in a string which is parsed into an instruction.
/// The instruction is then printed to check that it prints to the original
/// string. It is also encoded into a u16, which is then decoded to check the
/// resulting instruction is the same as the original.
///
/// The string can optionally be followed by "=>" and another string.
/// This checks that the printed string is identical to the second given string
/// when printed from the instruction. This is used to check the alternate
/// assembly forms of an instruction. The first string is therefore the
/// alternate form and the second is the default one.
///
/// The instruction can also be preceded by a parenthesis group containing first
/// an integer representing the address of the instruction, then any number of
/// 'symbol:address' pairs representing the addresses of symbols in the
/// instruction.
///
/// All the previous can optionally be followed by ":" and a u16 value.
/// If so, checks that encoding the instruction results in the exact same value.
macro_rules! test_assembly {
	(
		$(
			$(($addr0:literal $($id1:ident: $addr1:literal)+))?
			$asm:literal  $(=> $asm2:literal)? $(: $bin:literal)?
		)*
	) => {
		use super::*;

		#[allow(unreachable_code)]
		#[allow(unused_assignments)]
		#[allow(unused_mut)]
		#[allow(unused_variables)]
		#[test]
		fn assembly() {
			$(
				$(
					let mut addresses = std::collections::HashMap::new();
					$(
						addresses.insert(stringify!($id1), $addr1);
					)+
				)?
				let mut expected_bin = None;
				$(expected_bin = Some($bin);)?
				test_case($asm, test_assembly!{@prioritize $asm $($asm2)?},
					|start: Option<&str>, end: &str|{
						$(
							return addresses[end] - start.map_or($addr0, |st| addresses[st]);
						)?
						panic!("No symbols given.");
					},
					expected_bin
				);
			)*
		}
	};

	(
		@prioritize
		$asm:literal $asm2:literal
	) => {
		$asm2
	};

	(
		@prioritize
		$asm:literal
	) => {
		$asm
	};
}

mod alu;
mod alu2;
mod cap;
mod dup;
mod echo;
mod invalid;
mod jmp;
mod load;
mod misc;
mod pick;
mod req;
mod ret;
