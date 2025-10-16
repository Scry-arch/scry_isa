test_assembly! {
	"call 0" 					: 0b000000_0110000000
	"call 63" 					: 0b111111_0110000000

	(20 loc:36)
	"call loc"  => "call 7"
	(0 loc:128)
	"call loc"  => "call 63"
}
