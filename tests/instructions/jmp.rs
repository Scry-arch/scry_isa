test_assembly! {
	"jmp 0, 0"
	"jmp -1, 1"
	"jmp -64, 63"
	"jmp -64, 63"
	"jmp 0" => "jmp 0, 0"
	"jmp 1" => "jmp 0, 1"
	"jmp 64" => "jmp 1, 0"
	"jmp 3413" => "jmp 53, 21"
	"jmp 4159" => "jmp -64, 63"
	"jmp 8191" => "jmp -1, 63"

	(10 start:4 end:18)
	"jmp start, end"  => "jmp -3, 4"
	(14 end:18)
	"jmp 0, end"  => "jmp 0, 2"
	(26 start:2)
	"jmp start, 5"  => "jmp -12, 5"
	(8 end:14 after_end:24)
	"jmp after_end, end"  => "jmp 5, 3"
}
