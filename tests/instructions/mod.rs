use scry_isa::{Parser, Instruction};

/// Parses the given string into an instruction.
///
/// If parsing fails, returns the index of the token that caused the failure.
/// 0-indexed. Tokens are whitespace-delimited
fn parse_assembly(asm: &str, f: & impl Fn(Option<&str>, &str) -> i32) -> Result<Instruction, usize>
{
	let tokens: Vec<_> = asm.split_ascii_whitespace().collect();
	Instruction::parse(tokens.iter().cloned(), f).map(|(instr,..)| instr)
}

/// Tests the parsing of specific instruction.
///
/// An instruction is given in a string optionally followed by "=>" and another string.
///
/// If the string is alone (no "=>" etc) then it is parsed and printed.
/// It then checks whether the original and printed string are identical.
///
/// If the string is followed by another string (with "=>" between) it is parsed and printed.
/// It then checks that the printed string is identical to the second given string.
/// This is used to check the alternate assembly forms of an instruction.
/// The first string is therefore the alternate form and the second is the default one.
///
///
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
				let instr = parse_assembly($asm, &|start, end|{
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
				}).unwrap_or_else(|idx|
					panic!("Failed to parse '{}' at token '{}'", $asm, idx)
				);
				let mut buff = String::new();
				Instruction::print(&instr, &mut buff).unwrap();
				assert_eq!(test_assembly!{@prioritize $asm $($asm2)?}, buff);
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

mod jmp;
mod ret;
mod echo;
mod load;
mod alu;
mod alu2;