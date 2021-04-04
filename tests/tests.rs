use scry_isa::Parser;
mod instructions;

#[test]
fn test() {
	let (instr, _ ) = scry_isa::Instruction::parse(["jmp", "0,", "0"].iter().cloned()).unwrap();
	let mut buff = String::new();
	scry_isa::Instruction::print(&instr,&mut buff).unwrap();
	assert_eq!(buff, "jmp 0, 0");
	
	let (instr, _ ) = scry_isa::Instruction::parse(["ret", "3"].iter().cloned()).unwrap();
	let mut buff = String::new();
	scry_isa::Instruction::print(&instr,&mut buff).unwrap();
	assert_eq!(buff, "ret 3");
}
