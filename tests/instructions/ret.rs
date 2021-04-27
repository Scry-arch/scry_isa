test_assembly! {
	"ret 0"
	"ret 63"

	(20 loc:36)
	"ret loc"  => "ret 7"
	(0 loc:128)
	"ret loc"  => "ret 63"
}
