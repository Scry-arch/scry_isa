use scry_isa::{Instruction, Parser};

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
		match Instruction::parse(buffer.split(" ")) {
			Ok((instr2, _)) => {
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