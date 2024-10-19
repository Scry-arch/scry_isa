use scry_isa::ReferenceNode;

test_assembly! {
	(6 target1:14 target2: 14 )
	"inc =>(target1, target2)" => "inc =>3"
	(6 target:12 branch_at: 12 branch_to: 20 )
	"inc =>(target, branch_at=>branch_to)" => "inc =>2"
	(6 target:16 branch_at: 8 branch_to: 20 branch_target:28 )
	"inc =>(target, branch_at=>branch_to=>branch_target)" => "inc =>4"
	(6 branch1_at: 8 branch1_to: 20 target1: 24 branch2_at: 10 branch2_to: 30 target2: 32)
	"inc =>(branch1_at=>branch1_to=>target1, branch2_at=>branch2_to=>target2)" => "inc =>2"
	(16 branch_at: 20 branch_to1:100 target1:106 branch_to2:200 target2:206 )
	"inc =>branch_at=>(branch_to1=>target1, branch_to2=>target2)" => "inc =>4"
	(16 branch_at: 20 branch_to1:100 branch_at1: 110 branch_to2:200 branch_at2:210 target:1000 )
	"inc =>branch_at=>(branch_to1=>branch_at1, branch_to2=>branch_at2)=>target" => "inc =>6"
}
test_assembly_error! {
	(6 target2:14)
	"inc =>(target1, target2)" => ParseError {
		start_token: 1, start_idx: 3, end_token: 1, end_idx: 10,
		err_type: UnknownSymbol
	};

	(6 target1:14)
	"inc =>(target1, target2)" => ParseError {
		start_token: 2, start_idx: 0, end_token: 2, end_idx: 7,
		err_type: UnknownSymbol
	};

	(6 target1:12 target2: 14)
	"inc =>(target1=> branch_to, target2)" => ParseError {
		start_token: 2, start_idx: 0, end_token: 2, end_idx: 9,
		err_type: UnknownSymbol
	};

	(6 target1:12 target2: 14)
	"inc =>( target1, target2 => branch_to)" => ParseError {
		start_token: 5, start_idx: 0, end_token: 5, end_idx: 9,
		err_type: UnknownSymbol
	};

	(6 target1:12 target2: 14)
	"inc =>( target1 , target2 ) => branch_to" => ParseError {
		start_token: 7, start_idx: 0, end_token: 7, end_idx: 9,
		err_type: UnknownSymbol
	};

	"inc =>(3 | target2)" => ParseError {
		start_token: 2, start_idx: 0, end_token: 2, end_idx: 1,
		err_type: UnexpectedChars(",")
	};

	(6 target1:12 target2: 14 )
	"inc =>(target1 , target2," => ParseError {
		start_token: 3, start_idx: 7, end_token: 3, end_idx: 8,
		err_type: UnexpectedChars(")")
	};

	(6 target1:12 target2: 14 )
	"inc =>(target1 , target2" => ParseError {
		start_token: 4, start_idx: 0, end_token: 4, end_idx: 0,
		err_type: EndOfStream
	};

	(6 target1:12 target2: 14 )
	"inc =>(target1, target2)" => ParseError {
		start_token: 1, start_idx: 0, end_token: 2, end_idx: 8,
		err_type: UnequalReference(
			2, 3,
			vec!(ReferenceNode::Symbol("target1")),
			vec!(ReferenceNode::Symbol("target2"))
		)
	};

	(100 branch_from:120 branch_to:200 target1:220 target2: 120 )
	"inc =>(branch_from=>branch_to=>target1, target2)" => ParseError {
		start_token: 1, start_idx: 0, end_token: 2, end_idx: 8,
		err_type: UnequalReference(
			19, 9,
			vec!(
				ReferenceNode::Symbol("branch_from"),
				ReferenceNode::Symbol("branch_to"),
				ReferenceNode::Symbol("target1"),
			),
			vec!(ReferenceNode::Symbol("target2"))
		)
	};

	(100 branch_from:120 branch_to:200 target1:220 target2: 120 target3: 130 )
	"inc =>(branch_from=>branch_to=>target1=>target2, target2)=>target3" => ParseError {
		start_token: 1, start_idx: 0, end_token: 2, end_idx: 17,
		err_type: UnequalReference(
			24, 9,
			vec!(
				ReferenceNode::Symbol("branch_from"),
				ReferenceNode::Symbol("branch_to"),
				ReferenceNode::Symbol("target1"),
				ReferenceNode::Symbol("target2"),
				ReferenceNode::Symbol("target3"),
			),
			vec!(
				ReferenceNode::Symbol("target2"),
				ReferenceNode::Symbol("target3"),
			)
		)
	};

	(100 branch_from:120 branch_to:200 target1:180 target2: 120)
	"inc =>(branch_from=>branch_to=> target1, target2)" => ParseError {
		start_token: 1, start_idx: 0, end_token: 3, end_idx: 8,
		err_type: InvalidReference(
			Some(2),
			vec!(
				ReferenceNode::Symbol("branch_from"),
				ReferenceNode::Symbol("branch_to"),
				ReferenceNode::Symbol("target1"),
			),
		)
	};
}
