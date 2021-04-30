use scry_isa::{Instruction, ParseError, Parser};

/// Parses the given string into an instruction.
fn parse_assembly<'a>(
	asm: &'a str,
	f: &impl Fn(Option<&str>, &str) -> i32,
) -> Result<Instruction, ParseError<'a>>
{
	let tokens: Vec<_> = asm.split_ascii_whitespace().collect();
	Instruction::parse(tokens.iter().cloned(), f).map(|(instr, ..)| instr)
}

/// Tests that the given source assembly string parses (using the given
/// resolver) into an instruction that then prints into the expected assembly
/// string.
fn test_case<'a>(
	source_asm: &str,
	expected_asm: &str,
	resolver: &impl Fn(Option<&str>, &str) -> i32,
)
{
	let instr = parse_assembly(source_asm, resolver)
		.unwrap_or_else(|err| panic!("Failed to parse '{}': '{:?}'", source_asm, err));
	let mut buff = String::new();
	Instruction::print(&instr, &mut buff).unwrap();
	assert_eq!(buff, expected_asm, "From: \"{}\"", source_asm);
}

/// Tests the parsing of specific assembly instruction.
///
/// An instruction is given in a string optionally followed by "=>" and another
/// string.
/// If the string is alone (no "=>" etc) then it is parsed and printed.
/// It then checks whether the original and printed string are identical.
///
/// If the string is followed by another string (with "=>" between) it is parsed
/// and printed. It then checks that the printed string is identical to the
/// second given string. This is used to check the alternate assembly forms of
/// an instruction. The first string is therefore the alternate form and the
/// second is the default one.
///
/// The instruction can also be preceded by a parenthesis group containing first
/// an integer representing the address of the instruction, then any number of
/// 'symbol:address' pairs representing the addresses of symbols in the
/// instruction.
macro_rules! test_assembly {
	(
		$(
			$(($addr0:literal $($id1:ident: $addr1:literal)+))?
			$asm:literal  $(=> $asm2:literal)?
		)*
	) => {
		use super::*;

		#[allow(unreachable_code)]
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
				test_case($asm, test_assembly!{@prioritize $asm $($asm2)?}, &|start, end|{
					$(	return
						(	addresses[end] -
							if let Some(start) = start {
								addresses[start]
							} else {
								$addr0
							}
						);
					)?
					panic!("No symbols given.");
				});
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
mod jmp;
mod load;
mod pick;
mod ret;
