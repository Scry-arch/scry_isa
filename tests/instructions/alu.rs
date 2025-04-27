test_assembly! {
	"add =>0"								: 0b1000_0000_111_00000
	"add =>31"								: 0b1000_0000_111_11111
	"sub =>0"
	"sub =>1"
	"add =>2"
	"add =>3"
	"sub =>4"
	"sub =>5"
	"eq =>6"
	"eq =>7"
	"shr =>8"
	"shr =>9"
	"rol =>10"
	"rol =>11"
	"ror =>12"
	"ror =>13"
	"lt =>10"
	"and =>1"
	"or =>2"
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
	"shr =>branch=>branch_to=>branch2=>target" => "shr =>8"
	(12 branch:18 branch_to:60 branch2:70 branch_to2:100 target:120)
	"ror =>branch=>branch_to=>branch2=>branch_to2=>target" => "ror =>17"
}
