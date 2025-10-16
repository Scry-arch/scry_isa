test_assembly! {
	"add Low+High, =>31"						//: 0b0_11111_001_000_0001
	"add High+Low, =>0"							//: 0b0_00000_010_000_0001
	"add High+Low, =>" =>  "add High+Low, =>0"	//: 0b0_00000_010_000_0001
	"add Low=>High, =>24"						//: 0b0_11000_011_000_0001
	"add High=>Low, =>21"						//: 0b0_10101_100_000_0001
	"add Low, =>11"								//: 0b0_01011_101_000_0001
	"add High, =>1"								//: 0b0_00001_110_000_0001
	"sub High+Low, =>0"
	"sub Low+High, =>31"
	"sub High=>Low, =>7"
	"sub Low=>High, =>30"
	"sub High, =>5"
	"sub Low, =>18"
	"mul Low, =>23"
	"mul High+Low, =>13"
	"mul Low+High, =>27"
	"mul High=>Low, =>0"
	"mul Low=>High, =>20"
	"mul High, =>0"
	"mul Low, =>10"
	"shr High, =>15"
	"shl Low, =>16"
	"div Low, =>17"
}
