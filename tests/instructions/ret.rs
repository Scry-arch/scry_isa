test_assembly! {
	"ret 0"
	"ret 63"

	(20 loc:36)
	"ret loc"  => "ret 7"
	(0 loc:128)
	"ret loc"  => "ret 63"
}
test_assembly_error! {
	(100 loc:50)
	"ret loc"  => ParseError {
		start_token: 1, start_idx: 0, end_token: 1, end_idx: 3,
		err_type: OutOfBoundValue(-25, 0, 63) }
}
