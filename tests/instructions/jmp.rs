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
}