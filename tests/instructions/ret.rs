test_assembly! {
	"ret 0"
	"ret 63"

	(20 loc:36)
	"ret loc"  => "ret 8"
	(0 loc:126)
	"ret loc"  => "ret 63"
}
