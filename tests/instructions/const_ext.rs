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

test_assembly_error! {
	"const sadwij , 3" => ParseError {
		start_token: 1, start_idx: 0, end_token: 1, end_idx: 6,
		err_type: UnexpectedChars("integer scalar size") };
	"const sadwij, 3" => ParseError {
		start_token: 1, start_idx: 0, end_token: 1, end_idx: 7,
		err_type: UnexpectedChars("integer scalar size") };

	"const u0, unknown_label" => ParseError {
		start_token: 2, start_idx: 0, end_token: 2, end_idx: 13,
		err_type: UnknownSymbol };
	"const i0, unknown_label" => ParseError {
		start_token: 2, start_idx: 0, end_token: 2, end_idx: 13,
		err_type: UnknownSymbol };
	"const u0,unknown_label" => ParseError {
		start_token: 1, start_idx: 3, end_token: 1, end_idx: 16,
		err_type: UnknownSymbol };

	"const u0 som_leb" => ParseError {
		start_token: 2, start_idx: 0, end_token: 2, end_idx: 7,
		err_type: UnexpectedChars(",") };
	"const u1000 , unknown_label" => ParseError {
		start_token: 1, start_idx: 1, end_token: 1, end_idx: 5,
		err_type: OutOfBoundValue(1000, 0, 7) };
}
