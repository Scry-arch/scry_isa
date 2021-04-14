use scry_isa::{Instruction, Parser};
use quickcheck::{TestResult, Gen, Arbitrary};
use rand::seq::SliceRandom;

/// Tests that if we first print an instruction and then parse the printed text
/// we will get the exact same instruction as we started with.
#[quickcheck]
fn print_then_parse(instr: Instruction) -> bool
{
	let mut buffer = String::new();
	if let Err(err) = Instruction::print(&instr,&mut buffer) {
		println!("Failed to print instruction.\n Instruction: [{:?}]\n Error: {}", instr, err);
		false
	} else {
		match Instruction::parse(buffer.split(" "), &|_,_| unreachable!()) {
			Ok((instr2,..)) => {
				if instr != instr2 {
					println!("{:?} => {:?}", instr, instr2);
					false
				} else {
					true
				}
			},
			Err(idx) => {
				println!("Failed to parse instruction.\nText: '{}'\nError Index: {}", buffer, idx);
				false
			}
		}
	}
}

/// Tests that the number of tokens and bytes consumed by parsing is exactly equal
/// to the tokens in the instruction.
/// I.e. ensures that tokens after the instruction are ignored.
#[quickcheck]
fn consumes_only_instruction_tokens(instr: Instruction, extra: String) -> bool
{
	let mut buffer = String::new();
	Instruction::print(&instr,&mut buffer).unwrap();
	
	let instr_tokens: Vec<_> = buffer.split(" ").collect();
	let extra_tokens: Vec<_> = extra.split(" ").collect();
	
	let (_, consumed, bytes) = Instruction::parse(instr_tokens.iter().cloned().chain(extra_tokens.into_iter()), &|_,_| unreachable!()).unwrap();
	
	(consumed == (instr_tokens.len() - 1)) &&
		(bytes == instr_tokens.last().unwrap().len())
}

#[derive(Clone, Copy, Debug)]
enum CommaType {
	AtEnd, AtStart, InMiddle, Alone
}

impl Arbitrary for CommaType {
	fn arbitrary<G: Gen>(g: &mut G) -> Self {
		use CommaType::*;
		*[AtEnd, AtStart, InMiddle, Alone].choose(g).unwrap()
	}
}

/// Tests that all possible comma combinations are supported for any instruction
/// with commas:
/// 1. Comma as the end of a token with other text.
/// 1. Comma alone as a token.
/// 1. Comma as the start of a token with other text.
/// 1. Comma in the middle of a token, with text on both sides.
#[quickcheck]
fn different_commas(instr: Instruction, t1: CommaType, t_rest: Vec<CommaType>) -> quickcheck::TestResult
{
	let mut buffer = String::new();
	Instruction::print(&instr,&mut buffer).unwrap();
	
	// We make an infinite iterator producing comma types for use in the following loop.
	// We do this to ensure some variety to the types each match block gets.
	let mut comma_types = Some(t1).into_iter().chain(t_rest.into_iter()).cycle();
	
	if buffer.contains(",") {
		let mut new_buffer = String::new();
		
		for t in buffer.split(",") {
			use CommaType::*;
			if new_buffer.ends_with(" ") {
				// Is Alone or AtStart(of next token)
				match comma_types.next().unwrap() {
					AtEnd | InMiddle => {
						// Remove the space and replace with comma
						new_buffer.pop().unwrap();
						new_buffer.push(',');
					},
					_ => (),
				}
				new_buffer.push_str(t);
			} else {
				if t.starts_with(" ") {
					// Comma is AtEnd (of prev token) or Alone
					new_buffer.push(',');
					match comma_types.next().unwrap() {
						AtStart | InMiddle => {
							// Remove space
							new_buffer.push_str(&t[1..]);
						},
						_ => new_buffer.push_str(t),
					}
				} else if !new_buffer.is_empty(){
					// Comma is InMiddle
					match comma_types.next().unwrap() {
						AtStart => {
							new_buffer.push_str(" ,");
						},
						AtEnd => {
							new_buffer.push_str(", ");
						},
						Alone => {
							new_buffer.push_str(" , ");
						},
						InMiddle => new_buffer.push(','),
					}
					new_buffer.push_str(t)
				} else {
					assert!(new_buffer.is_empty());
					new_buffer.push_str(t)
				}
			}
		}
		TestResult::from_bool(Instruction::parse(new_buffer.split(" ").into_iter(), &|_,_| unreachable!()).is_ok())
	} else {
		TestResult::discard()
	}
}

/// Tests that if parsing fails because of bad syntax, the reported index is always within
/// the tokens of the instruction
#[quickcheck]
fn error_index_only_in_instruction(instr: Instruction, inject: char, mut inject_idx: usize, postfix: String) -> TestResult
{
	let mut buffer = String::new();
	Instruction::print(&instr,&mut buffer).unwrap();
	
	// We also count commas because they can be on their own, but the default
	// print puts at adjacent to teh previous token, which means space counting
	// doesn't count the comma.
	let instr_token_count = buffer.split(" ").count() + (buffer.split(",").count() - 1);

	// Inject string at next char boundary
	inject_idx = inject_idx % buffer.as_str().len();
	while !buffer.as_str().is_char_boundary(inject_idx) {
		inject_idx += 1;
	}
	buffer.insert(inject_idx, inject);
	
	buffer.push_str(postfix.as_str());
	
	Instruction::parse(buffer.split(" ").into_iter(), &|_,_| unreachable!()).map_or_else(
		|idx| TestResult::from_bool(idx < instr_token_count),
		|_| TestResult::discard())
}