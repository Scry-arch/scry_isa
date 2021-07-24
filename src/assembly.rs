use crate::{instructions::*, matchers::*};
use lazy_static::lazy_static;
use std::collections::HashMap;

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
                )*
            ]
            $($wip:tt)*
        ]
        ( $($instr:tt)* ) =
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
                    )*
                    @instruction [$($instr)*]
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
                    @parser [ $parser_type_done:ty ]
                    @result [ $parse_result_done:tt ]
                    @print_as [ $print_as_done:tt ]
                ])*
                @instruction [$($instr:tt)*]
                $(
                    @instruction [$($instr_rest:tt)*]
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
                        @parser [ $parser_type_done ]
                        @result [ $parse_result_done ]
                        @print_as [ $print_as_done ]
                    ])*
                    [
                        @instruction [$($instr)*]
                        @parser [ $parser_type ]
                        @result [ $parse_result ]
                        @print_as [ $print_as ]
                    ]
                    $(
                        @instruction [$($instr_rest)*]
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
                    @parser [ $parser_type_done:ty ]
                    @result [ $parse_result_done:tt ]
                    @print_as [ $print_as_done:tt ]
                ])*
                @instruction [$($instr:tt)*]
                $(
                    @instruction [$($instr_rest:tt)*]
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
                        @parser [ $parser_type_done ]
                        @result [ $parse_result_done ]
                        @print_as [ $print_as_done ]
                    ])*
                    [
                        @instruction [$($instr)*]
                        @parser [ $parser_type ]
                        @result [ $parse_result ]
                        @print_as [ $parse_result ]
                    ]
                    $(
                        @instruction [$($instr_rest)*]
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
        @indexify[$($prev:tt)*]
        @next_index[$idx:expr]
    ) => {
        map_mnemonics_impl!{
            @finalize
            $($prev)*
        }
    };

    (
        @finalize
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
        const INSTRUCTION_MNEMONICS: &'static [&'static str] = &[
            $($mnem),*
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

            fn parse<F>(
                mut tokens: impl Iterator<Item = &'a str> + Clone,
                f: &F,
            ) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
            where
                F: Fn(Option<&str>, &str) -> i32,
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
                    .find(|(mnemonic, _)| first_token.starts_with(*mnemonic))
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
                                if let Ok(($parse_result, consumed, bytes)) =
                                    <$parser_type>::parse(tokens.clone(), f)
                                    .or_else(|err| {
                                        furthest_error.replace_if_further(&err);
                                        Err(err)
                                    })
                                {
                                    Result::<(Instruction, usize, usize), ParseError>::Ok(($($instr)* , consumed, bytes))
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
                        |err: ParseError| Err(ParseError{
                            start_token: err.start_token + (consumed_first as usize),
                            start_idx: err.start_idx +
                                (((!consumed_first && (err.start_token == 0)) as usize)
                                    * mnemonic.len()),
                            end_token: err.start_token + (consumed_first as usize),
                            end_idx: err.end_idx +
                                (((!consumed_first && (err.end_token == 0)) as usize)
                                    * mnemonic.len()),
                            err_type: err.err_type
                        }),
                        |(instr, consumed, bytes)| Ok((
                            instr, consumed+((consumed_first && bytes != 0) as usize),
                            bytes + (mnemonic.len()*(!(consumed_first && bytes != 0) as usize)))
                        ))
                }else {
                    Err(ParseError::from_token(first_token, 0, ParseErrorType::UnexpectedChars("instruction mnemonic")))
                }
            }

            fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
            {
                use Instruction::*;

                out.write_str(Instruction::mnemonic(internal))?;

                match internal {
                    $(
                        $(
                            $($instr)* => {<$parser_type>::print_with_whitespace(& $print_as,true, out)}
                        )+
                    )*
                }
            }
        }
    };

    (@throw_out $($tokens:tt)*) =>{}
}

map_mnemonics! {
	"jmp"(Jump(imm, loc)) = {
		(imm, loc) <= Or<
			JumpOffsets,
			Offset<13,false>,
			_
		>
		=> (*imm, *loc)
	}
	"ret"(Call(CallVariant::Ret, loc)) = {
		loc = Offset<6,false>
	}
	"cap" (Capture(tar1,tar2)) = {
		(tar1,tar2) <= CommaBetween<
			ReferenceParser<5>,
			ReferenceParser<5>,
		> => (*tar1,*tar2)
	}
	"dup" (Duplicate(tar1,tar2,next)) = {
		(tar1,(tar2,next)) <= CommaBetween<
			ReferenceParser<5>,
			Then<
				ReferenceParser<5>,
				BoolFlag<Then<Comma, Alone<Arrow>>>
			>,
		> => (*tar1,(*tar2,*next))
	}
	"echo" (Echo(tar1,tar2,next)) = {
		(tar1,(tar2,next)) <= CommaBetween<
			ReferenceParser<5>,
			Then<
				ReferenceParser<5>,
				BoolFlag<Then<Comma, Alone<Arrow>>>
			>,
		> => (*tar1,(*tar2,*next))
	}
	(EchoLong(target)) = {
		target = ReferenceParser<10>
	}
	"inc"(Alu(AluVariant::Inc, target)) =
	"dec"(Alu(AluVariant::Dec, target)) =
	"rol"(Alu(AluVariant::RotateLeft, target)) =
	"ror"(Alu(AluVariant::RotateRight, target)) =
	{
		target = ReferenceParser<5>
	}
	"add"
	(Alu(AluVariant::Add, target)) =
	(Alu2(Alu2Variant::Add, output, target)) =
	"sub"
	(Alu(AluVariant::Sub, target)) =
	(Alu2(Alu2Variant::Sub, output, target)) =
	"shl"
	(Alu(AluVariant::ShiftLeft, target)) =
	(Alu2(Alu2Variant::ShiftLeft, output, target)) =
	"shr"
	(Alu(AluVariant::ShiftRight, target)) ={
		target = ReferenceParser<5>
	}
	(Alu2(Alu2Variant::ShiftRight, output, target)) ={
		(output, target) <= CommaBetween<
			Flatten<Then<
				Flag<Keyword<High>, Keyword<Low>>,
				Maybe<
					Then<Flag<Arrow, Plus>, Flag<Keyword<High>, Keyword<Low>>>
				>,
			>, _>,
			ReferenceParser<5>
		> => (*output, *target)
	}
	"pick" (Pick(imm, target)) = {
		(imm, target) <= Then<
			Maybe<
				Flatten<Then<Bits<5, false>, Comma>,_>
			>,
			ReferenceParser<5>
		> => (*imm, *target)
	}
	"ld" (Load(signed, size)) = {
		(signed, size) <= IntSize => (*signed, *size)
	}
	"st" (Store) = {
		() <= () => ()
	}
	"val" (Value(v)) = {
		v <= Or<
			ValueAlias,
			Bits<8, false>,
			_
		> => (*v)
	}
}
