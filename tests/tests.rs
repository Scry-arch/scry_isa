use scry_isa::Parser;
mod instructions;

#[test]
fn test() {
	let (instr, _ ) = scry_isa::InstructionParser::parse(&["jmp", "0,", "0"]).unwrap();
	let mut buff = String::new();
	scry_isa::InstructionParser::print(&instr,&mut buff).unwrap();
	assert_eq!(buff, "jmp 0, 0");
	
	let (instr, _ ) = scry_isa::InstructionParser::parse(&["ret", "3"]).unwrap();
	let mut buff = String::new();
	scry_isa::InstructionParser::print(&instr,&mut buff).unwrap();
	assert_eq!(buff, "ret 3");
}
