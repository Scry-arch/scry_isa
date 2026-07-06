test_assembly! {
	"jmp -1, 0" 							: 0b000000_1111111_100
	"jmp 0, 0" 								: 0b000000_0000000_100
	"jmp -1, 1" 							: 0b000001_1111111_100
	"jmp -64, 63" 							: 0b111111_1000000_100
	"jmp 0" => "jmp 0, 0"
	"jmp 1" => "jmp 0, 1"					: 0b000001_0000000_100
	"jmp 64" => "jmp 1, 0"					: 0b000000_0000001_100
	"jmp 3413" => "jmp 53, 21" 				: 0b010101_0110101_100
	"jmp 4159" => "jmp -64, 63"
	"jmp 8191" => "jmp -1, 63" 				: 0b111111_1111111_100

	(10 jmp_from:12)
	"jmp -1, jmp_from"  => "jmp -1, 0"		: 0b000000_1111111_100
	(10 jmp_from:12)
	"jmp 0, jmp_from"  => "jmp 0, 0"		: 0b000000_0000000_100
	(10 jmp_from:14)
	"jmp 0, jmp_from"  => "jmp 0, 1"		: 0b000001_0000000_100
	(10 jmp_from:14)
	"jmp 1, jmp_from"  => "jmp 1, 1"		: 0b000001_0000001_100

	(10 jmp_to:8)
	"jmp jmp_to, 0"  => "jmp -1, 0"			: 0b000000_1111111_100
	(10 jmp_to:10)
	"jmp jmp_to, 0"  => "jmp 0, 0"			: 0b000000_0000000_100
	(10 jmp_to:14)
	"jmp jmp_to, 0"  => "jmp 1, 0"			: 0b000000_0000001_100
	(10 jmp_to:16)
	"jmp jmp_to, 0"  => "jmp 2, 0"			: 0b000000_0000010_100

	(10 jmp_to:8 jmp_from:12)
	"jmp jmp_to, jmp_from"  => "jmp -1, 0"	: 0b000000_1111111_100
	(10 jmp_to:10 jmp_from:12)
	"jmp jmp_to, jmp_from"  => "jmp 0, 0"	: 0b000000_0000000_100
	(10 jmp_to:14 jmp_from:12)
	"jmp jmp_to, jmp_from"  => "jmp 1, 0"	: 0b000000_0000001_100
	(10 jmp_to:8 jmp_from:14)
	"jmp jmp_to, jmp_from"  => "jmp -1, 1"	: 0b000001_1111111_100
	(10 jmp_to:10 jmp_from:14)
	"jmp jmp_to, jmp_from"  => "jmp 0, 1"	: 0b000001_0000000_100
	(10 jmp_to:16 jmp_from:14)
	"jmp jmp_to, jmp_from"  => "jmp 1, 1"	: 0b000001_0000001_100

	(10 start:4 end:18)
	"jmp start, end"  => "jmp -3, 3"		: 0b000011_1111101_100
	(14 end:18)
	"jmp 0, end"  => "jmp 0, 1"
	(26 start:2)
	"jmp start, 5"  => "jmp -12, 5" 		: 0b000101_1110100_100
	(8 end:14 after_end:24)
	"jmp after_end, end"  => "jmp 5, 2" 	: 0b000010_0000101_100
}
