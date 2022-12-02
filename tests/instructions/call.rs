test_assembly! {
	"call 0"
	"call 63"

	(20 loc:36)
	"call loc"  => "call 7"
	(0 loc:128)
	"call loc"  => "call 63"
}
