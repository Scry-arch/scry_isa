test_assembly! {
	"const u0, 0"
	"const i0, 0"
	"const u0, 1"
	"const i0, 1"
	"const i0, -1"
	"const u0, 255"
	"const i0, -127"

	(10 start:120)
	"const u0, start" => "const u0, 120"
	(10 start:4 end:18)
	"const u0, start=>end" => "const u0, 14"
	(10 start:123 end:143)
	"const i0, start=>end" => "const i0, 20"
	(10 start:3 end:24)
	"const i0, end=>start" => "const i0, -21"
}
