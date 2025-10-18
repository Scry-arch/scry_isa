test_assembly! {
	"const u8, 0"		: 0b00000000_000_10000
	"const i8, 0"		: 0b00000000_001_10000
	"const u8, 1"		: 0b00000001_000_10000
	"const i8, 1"		: 0b00000001_001_10000
	"const i8, -1"		: 0b11111111_001_10000
	"const u8, 255"		: 0b11111111_000_10000
	"const i8, -127"	: 0b10000001_001_10000
	"const u16, 2"
	"const i16, 3"
	"const u32, 4"
	"const i32, 5"
	"const u64, 4"
	"const i64, 5"
	"const i16, 128" => "const i16, -128"
	"const i32, 196" => "const i32, -60"
	"const i64, 255" => "const i64, -1"

	"grow 0"			: 0b00000000_11000000
	"grow 22"			: 0b00010110_11000000
	"grow 255"			: 0b11111111_11000000

	(10 start:120)
	"const u8, start" => "const u8, 120"
	(10 start:4 end:18)
	"const u8, start=>end" => "const u8, 14"
	(10 start:123 end:143)
	"const i8, start=>end" => "const i8, 20"
	(10 start:3 end:24)
	"const i8, end=>start" => "const i8, -21"
}

test_assembly_error! {
	"const sadwij , 3" => ParseError {
		start_token: 1, start_idx: 0, end_token: 1, end_idx: 6,
		err_type: UnexpectedChars("integer scalar size") };
	"const sadwij, 3" => ParseError {
		start_token: 1, start_idx: 0, end_token: 1, end_idx: 7,
		err_type: UnexpectedChars("integer scalar size") };

	"const u8, unknown_label" => ParseError {
		start_token: 2, start_idx: 0, end_token: 2, end_idx: 13,
		err_type: UnknownSymbol };
	"const i8, unknown_label" => ParseError {
		start_token: 2, start_idx: 0, end_token: 2, end_idx: 13,
		err_type: UnknownSymbol };
	"const u8,unknown_label" => ParseError {
		start_token: 1, start_idx: 3, end_token: 1, end_idx: 16,
		err_type: UnknownSymbol };

	"const u8 som_leb" => ParseError {
		start_token: 2, start_idx: 0, end_token: 2, end_idx: 7,
		err_type: UnexpectedChars(",") };
	"const u128, unknown_label" => ParseError {
		start_token: 1, start_idx: 1, end_token: 1, end_idx: 4,
		err_type: OutOfBoundValue(128, 8, 64) };
	"const u1024, unknown_label" => ParseError {
		start_token: 1, start_idx: 1, end_token: 1, end_idx: 5,
		err_type: OutOfBoundValue(1024, 8, 64) };
}
