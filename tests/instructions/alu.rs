test_assembly! {
	"add =>0"		: 0b0_00000_111_000_0001
	"add =>31"		: 0b0_11111_111_000_0001
	"sub =>0"		: 0b0_00000_111_001_0001
	"sub =>1"		: 0b0_00001_111_001_0001
	"add =>2"		: 0b0_00010_111_000_0001
	"add =>3"		: 0b0_00011_111_000_0001
	"sub =>4"		: 0b0_00100_111_001_0001
	"sub =>5"		: 0b0_00101_111_001_0001
	"eq =>6"		: 0b0_00110_000_000_0001
	"eq =>7"		: 0b0_00111_000_000_0001
	"lt =>4"		: 0b0_00100_000_010_0001
	"gt =>29"		: 0b0_11101_111_010_0001
	"lt =>8"		: 0b0_01000_000_010_0001
	"gt =>9"		: 0b0_01001_111_010_0001
	"rol =>10"
	"rol =>11"
	"ror =>12"
	"ror =>13"
	"and =>1"		: 0b0_00001_000_001_0001
	"or =>2"		: 0b0_00010_000_011_0001
	"xor =>30"		: 0b0_11110_111_011_0001
	"isnar =>22"	: 0b0_10110_000_100_0001
	"narto =>23"	: 0b0_10111_111_100_0001
	"or =>" => "or =>0"

	(10 target:12)
	"add =>target" => "add =>0"
	(20 target:24)
	"sub =>target" => "sub =>1"
	(34 target:98)
	"add =>target" => "add =>31"
	(30 branch:32 branch_to:40)
	"sub =>branch=>branch_to" => "sub =>0"
	(30 branch:34 branch_to:40)
	"rol =>branch=>branch_to" => "rol =>1"
	(124 branch:130 branch_to:642 target:652)
	"gt =>branch=>branch_to=>target" => "gt =>7"
	(12 branch:20 branch_to:60 branch2:70 target:100)
	"xor =>branch=>branch_to=>branch2=>target" => "xor =>8"
	(12 branch:18 branch_to:60 branch2:70 branch_to2:100 target:120)
	"ror =>branch=>branch_to=>branch2=>branch_to2=>target" => "ror =>17"
}
