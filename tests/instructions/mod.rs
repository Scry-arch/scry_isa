use scry_isa::{Parser, Instruction};

/// Parses the given string into an instruction.
///
/// If parsing fails, returns the index of the token that caused the failure.
/// 0-indexed. Tokens are whitespace-delimited
fn parse_assembly(asm: &str) -> Result<Instruction, usize>
{
	let tokens: Vec<_> = asm.split_ascii_whitespace().collect();
	Instruction::parse(tokens.as_ref()).map(|(instr,_)| instr)
}

/// Tests snippets of assembly.
///
/// Input should be a set of strings, each of which is an instruction to be tested.
macro_rules! test_assembly {
	(
		$($asm: tt)*
	) => {
		use super::*;
		
		#[test]
		fn assembly() {
			$(
				let instr = parse_assembly($asm).unwrap_or_else(|idx|
					panic!("Failed to parse '{}' at token '{}'", $asm, idx)
				);
				let mut buff = String::new();
				Instruction::print(&instr, &mut buff).unwrap();
				assert_eq!($asm, buff);
			)*
		}
	}
}

mod jmp;