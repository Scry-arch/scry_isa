use crate::*;
use lazy_static::lazy_static;
use std::{borrow::Borrow, collections::HashMap, convert::TryInto};

/// Takes a definition of an instruction encoding and returns the filter and
/// mask needed to check if an instruction uses the given encoding.
///
/// The encoding is given from left to right in  bits from highest-order to
/// lowest-order. I.e. [0 1 1] produces the encoded instruction 0x011. All
/// encodings must be 16 bits.
///
/// The encoded instruction should first be AND'ed with the filter (first
/// result) to remove any fields from the test. Then the result is compared to
/// the mask (second result). If they are the same, then it's a match.
macro_rules! decode_filter_mask {

    (
        $($rest:tt)+
    ) => {
        decode_filter_mask_impl!([$($rest)+] [15] [0] [0])
    };
}
macro_rules! decode_filter_mask_impl {

    (
        []
        [$idx:expr]
        [$pre_filter:expr]
        [$pre_mask:expr]
    ) => {
        ($pre_filter, $pre_mask)
    };

    (
        [
            0 $($rest:tt)*
        ]
        [$idx:expr]
        [$pre_filter:expr]
        [$pre_mask:expr]
    ) => {
        decode_filter_mask_impl!(
            [$($rest)*]
            [($idx - 1)]
            [($pre_filter + (1 << $idx))]
            [$pre_mask]
        )
    };

    (
        [
            1 $($rest:tt)*
        ]
        [$idx:expr]
        [$pre_filter:expr]
        [$pre_mask:expr]
    ) => {
        decode_filter_mask_impl!(
            [$($rest)*]
            [($idx - 1)]
            [($pre_filter + (1 << $idx))]
            [($pre_mask + (1 << $idx))]
        )
    };

    (
        [
            [$field_name:ident : $field_size:expr] $($rest:tt)*
        ]
        [$idx:expr]
        [$pre_filter:expr]
        [$pre_mask:expr]
    ) => {
        decode_filter_mask_impl!(
            [$($rest)*]
            [($idx - $field_size)]
            [$pre_filter]
            [$pre_mask]
        )
    };
}

/// Assigns the value of an encoded instruction's fields to variables of the
/// same name. Assumes that the encoded instruction is of the given encoding.
/// Should use `decode_filter_mask` to check first.
macro_rules! decode_fields {

    (
        $encoded:expr => $($rest:tt)+
    ) => {
        decode_fields_impl!([$($rest)+] [15] [] [$encoded])
    };
}
macro_rules! decode_fields_impl {

    (
        []
        [$idx:expr]
        [$($pre:tt)*]
        [$encoded:expr]
    ) => {
        $($pre)*
    };

    (
        [
            $bit:literal $($rest:tt)*
        ]
        [$idx:expr]
        [$($pre:tt)*]
        [$encoded:expr]
    ) => {
        decode_fields_impl!(
            [$($rest)*]
            [($idx - 1)]
            [$($pre)*]
            [$encoded]
        )
    };

    (
        [
            [$field_name:ident : $field_size:expr] $($rest:tt)*
        ]
        [$idx:expr]
        [$($pre:tt)*]
        [$encoded:expr]
    ) => {
        decode_fields_impl!(
            [$($rest)*]
            [($idx - $field_size)]
            [$($pre)*
                let $field_name = Bits::<$field_size, false>{value:
                    (($encoded & (((1 << $field_size) - 1) << ($idx-$field_size+1))) >> ($idx-$field_size+1)) as i32
                }.try_into().unwrap();

            ]
            [$encoded]
        )
    };
}

/// Encodes an instruction with the given encoding. Returns the encoded value.
/// Assumes variables exist matching the names of the fields in the encoding.
macro_rules! encode_fields {

    (
        $($rest:tt)+
    ) => {
        encode_fields_impl!([$($rest)+] [15] [ decode_filter_mask!($($rest)+).1 ] )
    };
}
macro_rules! encode_fields_impl {

    (
        []
        [$idx:expr]
        [$($pre:tt)*]
    ) => {
        $($pre)*
    };

    (
        [
            $bit:literal $($rest:tt)*
        ]
        [$idx:expr]
        [$($pre:tt)*]
    ) => {
        encode_fields_impl!(
            [$($rest)*]
            [($idx - 1)]
            [$($pre)*]
        )
    };

    (
        [
            [$field_name:ident : $field_size:expr] $($rest:tt)*
        ]
        [$idx:expr]
        [$($pre:tt)*]
    ) => {
        encode_fields_impl!(
            [$($rest)*]
            [($idx - $field_size)]
            [$($pre)* + ((((Bits::<$field_size,false>::from(*$field_name)).value & ((1 << $field_size)-1))as u16) << ($idx-$field_size+1))]
        )
    };
}

macro_rules! map_mnemonics {

    (
        $mnem1:literal
        $($rest:tt)+
    ) => {
        map_mnemonics_impl!{
            @extract[]
            @wip[]
            $mnem1
            $($rest)+
        }
    };
}

macro_rules! map_mnemonics_impl {

    (
        @extract []
        @wip[]
        $mnem:literal
        $($rest:tt)*
    ) => {
        map_mnemonics_impl!{
            @extract []
            @wip[
                [
                    @mnemonic [ $mnem ]
                ]
            ]
            $($rest)*
        }
    };

    (
        @extract [$($extracted:tt)*]
        @wip [
            $([
                @mnemonic [ $mnem_old:literal ]
                $([
                    @instruction [$($instr:tt)*]
                    @encoding [ $($enc:tt)* ]
                    @parser [ $parser_type:ty ]
                    @result [ $parse_result:tt ]
                    @print_as [ $print_as:tt ]
                ])+
            ])+
        ]
        $mnem:literal
        $($rest:tt)*
    ) => {
        map_mnemonics_impl!{
            @extract[
                $($extracted)*
                $([
                    @mnemonic [ $mnem_old ]
                    $([
                        @instruction [$($instr)*]
                        @encoding [ $($enc)* ]
                        @parser [ $parser_type ]
                        @result [ $parse_result ]
                        @print_as [ $print_as ]
                    ])+
                ])+
            ]
            @wip [
                [
                    @mnemonic [ $mnem ]
                ]
            ]
            $($rest)*
        }
    };

    (
        @extract [$($extracted:tt)*]
        @wip [
            $([
                @mnemonic [ $mnem_old:literal ]
                $(
                    @instruction [$($instr:tt)*]
                    @encoding [ $($enc:tt)* ]
                )+
            ])+
        ]
        $mnem:literal
        $($rest:tt)*
    ) => {
        map_mnemonics_impl!{
            @extract[
                $($extracted)*
            ]
            @wip [
                [
                    @mnemonic [ $mnem ]
                ]
                $([
                    @mnemonic [ $mnem_old ]
                    $(
                        @instruction [$($instr)*]
                        @encoding [ $($enc)* ]
                    )+
                ])+
            ]
            $($rest)*
        }
    };

    (
        @extract [$($extracted:tt)*]
        @wip [
            [
                @mnemonic [ $mnem:literal ]
                $([$($instructions_done:tt)*])*
                $(
                    @instruction [$($instr_old:tt)*]
                    @encoding [ $($enc_old:tt)* ]
                )*
            ]
            $($wip:tt)*
        ]
        ( $($instr:tt)* ) [ $($enc:tt)* ]
        $($rest:tt)*
    ) => {
        map_mnemonics_impl!{
            @extract [$($extracted)*]
            @wip [
                [
                    @mnemonic [ $mnem ]
                    $([$($instructions_done)*])*
                    $(
                        @instruction [$($instr_old)*]
                        @encoding [ $($enc_old)* ]
                    )*
                    @instruction [$($instr)*]
                    @encoding [ $($enc)* ]
                ]
                $($wip)*
            ]
            $($rest)*
        }
    };

    (
        @extract [$($extracted:tt)*]
        @wip [
            $([
                @mnemonic [ $mnem:literal ]
                $([
                    @instruction [$($instr_done:tt)*]
                    @encoding [ $($enc_done:tt)* ]
                    @parser [ $parser_type_done:ty ]
                    @result [ $parse_result_done:tt ]
                    @print_as [ $print_as_done:tt ]
                ])*
                @instruction [$($instr:tt)*]
                @encoding [ $($enc:tt)* ]
                $(
                    @instruction [$($instr_rest:tt)*]
                    @encoding [ $($enc_rest:tt)* ]
                )*
            ])+
        ]
        {
            $parse_result:tt <= $parser_type:ty  => $print_as:tt
        }
        $($rest:tt)*
    ) => {
        map_mnemonics_impl!{
            @extract [$($extracted)*]
            @wip [
                $([
                    @mnemonic [ $mnem ]
                    $([
                        @instruction [$($instr_done)*]
                        @encoding [ $($enc_done)* ]
                        @parser [ $parser_type_done ]
                        @result [ $parse_result_done ]
                        @print_as [ $print_as_done ]
                    ])*
                    [
                        @instruction [$($instr)*]
                        @encoding [ $($enc)* ]
                        @parser [ $parser_type ]
                        @result [ $parse_result ]
                        @print_as [ $print_as ]
                    ]
                    $(
                        @instruction [$($instr_rest)*]
                        @encoding [ $($enc_rest)* ]
                    )*
                ])+
            ]
            $($rest)*
        }
    };

    (
        @extract [$($extracted:tt)*]
        @wip [
            $([
                @mnemonic [ $mnem:literal ]
                $([
                    @instruction [$($instr_done:tt)*]
                    @encoding [ $($enc_done:tt)* ]
                    @parser [ $parser_type_done:ty ]
                    @result [ $parse_result_done:tt ]
                    @print_as [ $print_as_done:tt ]
                ])*
                @instruction [$($instr:tt)*]
                @encoding [ $($enc:tt)* ]
                $(
                    @instruction [$($instr_rest:tt)*]
                    @encoding [ $($enc_rest:tt)* ]
                )*
            ])+
        ]
        {
            $parse_result:tt = $parser_type:ty
        }
        $($rest:tt)*
    ) => {
        map_mnemonics_impl!{
            @extract [$($extracted)*]
            @wip [
                $([
                    @mnemonic [ $mnem ]
                    $([
                        @instruction [$($instr_done)*]
                        @encoding [ $($enc_done)* ]
                        @parser [ $parser_type_done ]
                        @result [ $parse_result_done ]
                        @print_as [ $print_as_done ]
                    ])*
                    [
                        @instruction [$($instr)*]
                        @encoding [ $($enc)* ]
                        @parser [ $parser_type ]
                        @result [ $parse_result ]
                        @print_as [ $parse_result ]
                    ]
                    $(
                        @instruction [$($instr_rest)*]
                        @encoding [ $($enc_rest)* ]
                    )*
                ])+
            ]
            $($rest)*
        }
    };

    (
        @extract [$($extracted:tt)*]
        @wip[$($wip:tt)*]
    ) => {
        map_mnemonics_impl!{
            @indexify[]
            @next_index [ 0 ]
            $($extracted)*
            $($wip)*
        }
    };

    (
        @indexify[$($prev:tt)*]
        @next_index [ $idx:expr ]
        [
            @mnemonic [ $mnem1:literal ]
            $([
                @instruction [$($instr1:tt)*]
                @encoding [ $($enc1:tt)* ]
                @parser [ $parser_type1:ty ]
                @result [ $parse_result1:tt ]
                @print_as [ $print_as1:tt ]
            ])+
        ]
        $($rest:tt)*
    ) => {
        map_mnemonics_impl!{
            @indexify[
                $($prev)*
                [
                    @index [ $idx ]
                    @mnemonic [ $mnem1 ]
                    $([
                        @instruction [$($instr1)*]
                        @encoding [ $($enc1)* ]
                        @parser [ $parser_type1 ]
                        @result [ $parse_result1 ]
                        @print_as [ $print_as1 ]
                    ])+
                ]
            ]
            @next_index[ $idx + 1 ]
            $($rest)*
        }
    };

    (
        @indexify[
            $( [
                @index [ $idx:expr ]
                @mnemonic [ $mnem:literal ]
                $([
                    @instruction [$($instr:tt)*]
                    @encoding [ $($enc:tt)* ]
                    @parser [ $parser_type:ty ]
                    @result [ $parse_result:tt ]
                    @print_as [ $print_as:tt ]
                ])+
            ])*
        ]
        @next_index[$next_idx:expr]
    ) => {
        map_mnemonics_impl!{
            @finalize
            @parser
            $( [
                @index [ $idx ]
                @mnemonic [ $mnem ]
                $([
                    @instruction [$($instr)*]
                    @parser [ $parser_type ]
                    @result [ $parse_result ]
                    @print_as [ $print_as ]
                ])+
            ])*
            [ // Add a parser for invalid instructions
                @index [ $next_idx ]
                @mnemonic [ "invalid" ]
                [
                    @instruction [Invalid(enc)]
                    @parser [ u16 ]
                    @result [ enc ]
                    @print_as [ enc ]
                ]
            ]
        }
        map_mnemonics_impl!{
            @finalize
            @encoder
            $(
                $([
                    @instruction [$($instr)*]
                    @encoding [ $($enc)* ]
                ])+
            )*
            // We don't add an encoder for invalid instructions
            // as they are treated in a special way during encoding/decoding
        }
    };

    (
        @finalize
        @parser
        $( [
            @index [ $idx:expr ]
            @mnemonic [ $mnem:literal ]
            $([
                @instruction [$($instr:tt)*]
                @parser [ $parser_type:ty ]
                @result [ $parse_result:tt ]
                @print_as [ $print_as:tt ]
            ])+
        ])*
    ) => {
        pub const INSTRUCTION_MNEMONICS: &'static [&'static str] = &[
            $($mnem,)*
        ];

        impl Instruction {
            /// Returns the mnemonic for this instruction.
            /// I.e. the mnemonic for load instructions if "ld".
            pub fn mnemonic(&self) -> &'static str
            {
                use Instruction::*;
                #[allow(unused_variables)]
                match self {
                    $($($($instr)* => INSTRUCTION_MNEMONICS[$idx],)+)*
                }
            }
        }

        impl<'a> Parser<'a> for Instruction
        {
            type Internal = Instruction;
            const ALONE_RIGHT: bool = true;
            const ALONE_LEFT: bool = true;

            fn parse<I,F,B>(
                mut tokens: I,
                f: B,
            ) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
            where
                I: Iterator<Item = &'a str> + Clone,
                B: Borrow<F>,
                F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
            {
                use Instruction::*;
                lazy_static!{
                    static ref MNEMONIC_PARSERS: HashMap<&'static str, u16> = {
                        let mut mnem_pars:  HashMap<&'static str, u16>  = HashMap::new();
                        $(
                            mnem_pars.insert($mnem, $idx);
                        )*
                        mnem_pars
                    };
                }

                let first_token = tokens.next()
                    .ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))?;
                if let Some((mnemonic, parser_idx)) = MNEMONIC_PARSERS.iter()
                    .find(|(mnemonic, _)| {
                        first_token.starts_with(*mnemonic) &&
                        // Make sure the next char is not a valid char for symbols
                        first_token.chars().nth(mnemonic.len()).map_or(true , |c|
                        !c.is_ascii_alphanumeric() && c != '_' && c != '.' && c.is_ascii()
                        )
                    })
                {
                    let consumed_first = first_token.len() == mnemonic.len();
                    let tokens = Some(first_token.split_at(mnemonic.len()).1).into_iter()
                        .filter(|t| !t.is_empty()).chain(tokens);

                    $(
                        if *parser_idx == ($idx) {
                            let mut furthest_error = ParseError{
                                start_token: 0, start_idx: 0,
                                end_token: usize::MAX, end_idx: usize::MAX,
                                err_type: ParseErrorType::InternalError(concat!(file!(), ':', line!()))
                            };
                            $(
                                if let Ok(($parse_result, consumed)) =
                                    <$parser_type>::parse::<_,F,_>(tokens.clone(), f.borrow())
                                    .or_else(|err| {
                                        furthest_error.replace_if_further(&err);
                                        Err(err)
                                    })
                                {
                                    Result::<(Instruction, CanConsume), ParseError>::Ok(($($instr)* , consumed))
                                } else
                            )+
                            {
                                Err(furthest_error)
                            }
                        } else
                    )*
                    {
                        unreachable!()
                    }
                    .map_or_else(
                        |mut err: ParseError| {
                            let consumed = if consumed_first {
                                Consumed{tokens: 1, chars: 0}
                            } else {
                                Consumed::none()
                            };
                            consumed.advance_err(&mut err);
                            Err(err)
						},
                        |(instr, consumed)| Ok((
                            instr,
                            CanConsume {
                                tokens: consumed.tokens+((consumed_first && consumed.chars != 0) as usize),
                                chars: consumed.chars + (mnemonic.len()*(!(consumed_first && consumed.chars != 0) as usize))
                            }
                        )))
                } else {
                    Err(ParseError::from_token(first_token, 0, 0, ParseErrorType::UnexpectedChars("instruction mnemonic")))
                }
            }

            fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
            {
                use Instruction::*;

                out.write_str(Instruction::mnemonic(internal))?;
                out.write_char(' ')?;

                match internal {
                    $(
                        $(
                            $($instr)* => {<$parser_type>::print_with_whitespace(& $print_as,false, out)}
                        )+
                    )*
                }
            }
        }
    };

    (
        @finalize
        @encoder
        $([
            @instruction [$($instr:tt)*]
            @encoding [ $($enc:tt)* ]
        ])+
    ) => {
        impl Instruction
        {
            pub fn decode(binary: u16) -> Self
            {
                $(
                    {
                        let (filter, mask) = decode_filter_mask!($($enc)*);
                        if (binary & filter) == mask {
                            // instruction found
                            decode_fields!(binary => $($enc)*);
                            return Instruction::$($instr)*;
                        }
                    }
                )+
                // If none of the above match, return invalid
                Instruction::Invalid(binary)
            }
            pub fn encode(&self) -> u16
            {
                match self {
                    $(
                        Instruction::$($instr)* => {
                            encode_fields!($($enc)*)
                        }
                    )+
                    Instruction::Invalid(enc) => *enc,
                }
            }
        }
    };
}

map_mnemonics! {
	"jmp"(Jump(imm, trig)) [ [trig:6] [imm:7] 1 0 0 ]
	{
		(imm, trig) <= Or<
			JumpOffsets,
			Offset<13,false>,
			_
		>
		=> (*imm, *trig)
	}
	"call"(Call(CallVariant::Call, trig)) [ [trig:6] 0 1 1 0 0 0 0 0 0 0 ]
	{
		trig = Offset<6,false>
	}
	"ret"(Call(CallVariant::Ret, trig)) [ [trig:6] 1 1 1 0 0 0 0 0 0 0 ]
	{
		trig = Offset<6,false>
	}
	"dup" (Duplicate(next, ref1,ref2)) [ [next:1] [ref1:5] [ref2:5] 1 1 0 0 1 ]
	{
		(ref1,(ref2,next)) <= CommaBetween<
			ReferenceParser<5>,
			Then<
				ReferenceParser<5>,
				BoolFlag<Then<Comma, Alone<Arrow>>>
			>,
		> => (*ref1,(*ref2,*next))
	}
	"echo" (Echo(next,ref1,ref2)) [ [next:1] [ref1:5] [ref2:5] 0 1 0 0 1 ]
	{
		(ref1,(ref2,next)) <= CommaBetween<
			ReferenceParser<5>,
			Then<
				ReferenceParser<5>,
				BoolFlag<Then<Comma, Alone<Arrow>>>
			>,
		> => (*ref1,(*ref2,*next))
	}
	(EchoLong(refl)) [ [refl:10] 0 1 0 0 1 0 ]
	{
		refl = ReferenceParser<10>
	}
	//                                                          MOD    FUNC
	"rol"(Alu(AluVariant::RotateLeft, ref1))      [ 0 [ref1:5] 0 0 0  1 0 1  0 0 0 1 ]
	"ror"(Alu(AluVariant::RotateRight, ref1))     [ 0 [ref1:5] 1 1 1  1 0 1  0 0 0 1 ]
	"and"(Alu(AluVariant::BitAnd, ref1))          [ 0 [ref1:5] 0 0 0  0 0 1  0 0 0 1 ]
	"or"(Alu(AluVariant::BitOr, ref1))            [ 0 [ref1:5] 0 0 0  0 1 1  0 0 0 1 ]
	"xor"(Alu(AluVariant::BitXor, ref1))          [ 0 [ref1:5] 1 1 1  0 1 1  0 0 0 1 ]
	"eq"(Alu(AluVariant::Equal, ref1))            [ 0 [ref1:5] 0 0 0  0 0 0  0 0 0 1 ]
	"lt"(Alu(AluVariant::LessThan, ref1))         [ 0 [ref1:5] 0 0 0  0 1 0  0 0 0 1 ]
	"gt"(Alu(AluVariant::GreaterThan, ref1))      [ 0 [ref1:5] 1 1 1  0 1 0  0 0 0 1 ]
	"isnar"(Alu(AluVariant::IsNar, ref1))         [ 0 [ref1:5] 0 0 0  1 0 0  0 0 0 1 ]
	"narto"(Alu(AluVariant::NarTo, ref1))         [ 0 [ref1:5] 1 1 1  1 0 0  0 0 0 1 ]
	{
		ref1 = ReferenceParser<5>
	}
	"add"
	(Alu(AluVariant::Add, ref1))                  [ 0 [ref1:5] 1 1 1  0 0 0  0 0 0 1 ]
	(Alu2(Alu2Variant::Add, mod_f, ref1))         [ 0 [ref1:5] [mod_f:3]  0 0 0  0 0 0 1 ]
	"sub"
	(Alu(AluVariant::Sub, ref1))                  [ 0 [ref1:5] 1 1 1  0 0 1  0 0 0 1 ]
	{
		ref1 = ReferenceParser<5>
	}
	(Alu2(Alu2Variant::Sub, mod_f, ref1))         [ 0 [ref1:5] [mod_f:3]  0 0 1  0 0 0 1 ]
	{
		(mod_f, ref1) <= Alu2Ref => (*mod_f, *ref1)
	}
	"shl"
	(Alu2(Alu2Variant::ShiftLeft, mod_f, ref1)) [ 0 [ref1:5] [mod_f:3]  0 1 0  0 0 0 1 ]
	"shr"
	(Alu2(Alu2Variant::ShiftRight, mod_f, ref1))[ 0 [ref1:5] [mod_f:3]  0 1 1  0 0 0 1 ]
	"mul"
	(Alu2(Alu2Variant::Multiply, mod_f, ref1))  [ 0 [ref1:5] [mod_f:3]  1 0 0  0 0 0 1 ]
	"div"
	(Alu2(Alu2Variant::Division, mod_f, ref1))  [ 0 [ref1:5] [mod_f:3]  1 0 1  0 0 0 1 ]
	{
		(mod_f, ref1) <= Alu2Ref => (*mod_f, *ref1)
	}
	"pick" (Pick(ref1)) [ 0 [ref1:5] 0 0 0 0 0 0 0 0 1 0 ]
	{
		ref1 = ReferenceParser<5>
	}
	(PickI(imm, ref1)) [ 1 [ref1:5] [imm:2] 0 0 0 0 0 0 1 0 ]
	{
		(imm, ref1) <= CommaBetween<
			Bits<2, false>,
			ReferenceParser<5>
		> => (*imm, *ref1)
	}
	"cast"
	(Cast(type_f, ref1)) [ 1 [ref1:5] [type_f:4] 1 0 0 0 1 0 ]
	{
		(type_f, ref1 )<= CommaBetween<
			TypeMatcher<4,3>,
			ReferenceParser<5>
		> => (*type_f, *ref1)
	}
	"ld"
	(Load(type_f, ref1)) [ 0 [ref1:5] [type_f:4] 1 0 0 0 1 0 ]
	{
		(type_f, ref1 )<= CommaBetween<
			TypeMatcher<4,3>,
			ReferenceParser<5>
		> => (*type_f, *ref1)
	}
	(LoadStack(type_f, index)) [ 0 [index:5] [type_f:4] 1 0 0 0 0 0 ]
	{
		(type_f, index )<= Then<
			TypeMatcher<4,3>,
			MemIndex
		> => (*type_f, *index)
	}
	"st"
	(StoreStack(index)) [ 0 [index:5] 0 0 1 0 0 0 0 0 0 0 ]
	{
		index <=
			MemIndex
		=> (*index)
	}
	(Store) [ 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]
	{
		() = ()
	}
	"nop" (NoOp)  [ 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]
	"trap" (Trap)  [ 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ]
	{
		() = ()
	}
	"const"
	(Constant(typ, imm)) [[imm:8] [typ:3] 1 0 0 0 0 ]
	{
		(typ, (imm, _)) <= CommaBetween<
			TypeMatcher<3,2>,
			Signless<8>,
		> => (*typ, (*imm, TryInto::<Type>::try_into(*typ).unwrap().is_signed_int()))
	}
	"grow"
	(Grow(imm)) [[imm:8] 1 1 0 0 0 0 0 0 ]
	{
		imm <= Bits<8, false> => (*imm)
	}
	"saddr"
	(StackAddr(size, index)) [ 0 [index:5] [size:2] 0 1 0 0 0 0 0 0 ]
	{
		(size, index )<= Then<
			Bits<2, false>,
			MemIndex
		> => (*size, *index)
	}
	"rsrv"
	(StackRes(true, bytes, base)) [ 1 1 [bytes:4] [base:1] 0 0 0 0 0 0 0 0 0 ]
	{
		(bytes, base)<= Then<
			Pow2<4>,
			BoolFlag<Prefix<Comma, Base>>,
		> => (*bytes, *base)
	}
	"free"
	(StackRes(false, bytes, base)) [ 1 1 [bytes:4] [base:1] 1 0 0 0 0 0 0 0 0 ]
	{
		(bytes, base)<= Then<
			Pow2<4>,
			BoolFlag<Prefix<Comma, Base>>,
		> => (*bytes, *base)
	}
}
