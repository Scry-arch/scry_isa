test_assembly! {
	"inc =>0"								: 0b1000_0000_000_00000
	"inc =>31"								: 0b1000_0000_000_11111
	"dec =>0"
	"dec =>1"
	"add =>2"
	"add =>3"
	"sub =>4"
	"sub =>5"
	"shl =>6"
	"shl =>7"
	"shr =>8"
	"shr =>9"
	"rol =>10"
	"rol =>11"
	"ror =>12"
	"ror =>13"
	"mul =>10"
	"and =>1"
	"or =>2"
	"or =>" => "or =>0"

	(10 target:12)
	"inc =>target" => "inc =>0"
	(20 target:24)
	"dec =>target" => "dec =>1"
	(34 target:98)
	"add =>target" => "add =>31"
	(30 branch:32 branch_to:40)
	"sub =>branch=>branch_to" => "sub =>0"
	(30 branch:34 branch_to:40)
	"rol =>branch=>branch_to" => "rol =>1"
	(124 branch:130 branch_to:642 target:652)
	"shl =>branch=>branch_to=>target" => "shl =>7"
	(12 branch:20 branch_to:60 branch2:70 target:100)
	"shr =>branch=>branch_to=>branch2=>target" => "shr =>8"
	(12 branch:18 branch_to:60 branch2:70 branch_to2:100 target:120)
	"ror =>branch=>branch_to=>branch2=>branch_to2=>target" => "ror =>17"

	// (6 target1:14 target2: 14 )
	// "inc =>(target1, target2)" => "inc =>3"
	// (6 branch_at: 8 target:12 branch_to: 20 )
	// "inc =>(target, branch_at=>branch_to)" => "inc =>2"
	// (6 branch_at: 8 target:16 branch_to: 20 branch_target:24 )
	// "inc =>(target, branch_at=>branch_to=>branch_target)" => "inc =>4"
	// (6 branch1_at: 8 branch1_to: 20 target1: 24 branch2_at: 10 branch1_to: 30 target2: 32)
	// "inc =>(branch1_at=>branch1_to=>target1, branch2_at=>branch2_to=>target2)" => "inc =>4"
	// (16 branch_at: 20 branch_to1:100 target1:106 branch_to2:200 target1:206 )
	// "inc =>branch_at=>(branch_to1=>target1, branch_to2=>target2)" => "inc =>5"
	// (16 branch_at: 20 branch_to1:100 branch_at1: 110 branch_to2:200 branch_at2:210 target:1000 )
	// "inc =>branch_at=>(branch_to1=>branch_at1, branch_to2=>branch_at2)=>target" => "inc =>6"
}
