use crate::*;
use lazy_static::lazy_static;
use std::{borrow::Borrow, collections::HashMap, convert::TryInto};

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
        const INSTRUCTION_MNEMONICS: &'static [&'static str] = &[
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
                        |(instr, consumed)| Ok((
                            instr,
                            CanConsume {
                                tokens: consumed.tokens+((consumed_first && consumed.chars != 0) as usize),
                                chars: consumed.chars + (mnemonic.len()*(!(consumed_first && consumed.chars != 0) as usize))
                            }
                        )))
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

    (
        @finalize
        @encoder
        $([
            @instruction [$($instr:tt)*]
            @encoding [ $($enc:tt)* ]
        ])+
    ) => {
        impl_encoding!{
            @init [Fsm Instruction Invalid]
            $(
                ($($instr)*) [ $($enc)* ]
            )+
        }

        impl Instruction
        {
            pub fn decode(binary: u16) -> Self
            {
                Fsm::decode_from(binary,0)
            }
            pub fn encode(&self) -> u16
            {
                if let Some(encoder) = Fsm::new_encode(self) {
                    let mut result = 0;
                    encoder.encode_from(&mut result, 0);
                    result
                } else {
                    if let Instruction::Invalid(enc) = self {
                        *enc
                    } else {
                        unreachable!()
                    }
                }
            }
        }
    };
}

/// Implements Finite-State-Machine-based enum encoding/decoding.
///
/// First "@init" must be given with a "[]" containing:
///
/// 1. The desired name for the encoder/decoder enum.
/// 2. The name of the enum to be encoded/decoded.
/// 3. An expression. This expression must be callable with a u16 to produce the
/// desired enum variant for when decoding fails (or panics). The expression may
/// therefore be e.g. a closure accepting u16 or simply the name of a enum
/// variant with a u16 member.
///
/// Thereafter the encoding of the enum follows.
/// It must be given using a list of enum variants inside "()" followed by their
/// encoding pattern within "[]".
///
/// An encoding pattern is a list of "0", "1", wildcards, or groups.
/// The first element in the list specifies what the value of the
/// most-significant bit in the variant encoding should be. I.e. if "0" is
/// given, the most significant bit must be 0. The next elements encode the less
/// significant bits in order.
///
/// In the following example, V1 is encoded as 0b010 (2), V2 as 0b011 (3) and V3
/// as 0b100 (4):
///
/// ```no_a_doc_test
/// (V1)    [0 1 0]
/// (V2)    [0 1 1]
/// (V3)    [1 0 0]
/// ```
///
/// A wildcard allows the given bit(s) to be any value. A wildcard is a "[]"
/// within which first an identifier is given, then ":", then a number. The
/// number signifies how many bits are accepted by the wildcard. The current bit
/// is the most significant bit accepted by the wildcard. E.g. "[offset:3]"
/// accepts any value for the current bit and the next 2 less significant bits.
///
/// An example invocation could be:
///
/// ```no_a_doc_test
/// (V1(wild1, wild2))          [0 1 0 [wild1:7] [wild2:6] ]
/// (V2(wild1, wild2, wild3))   [0 1 1 [wild1:5] [wild2:5] [wild3:1] ]
/// (V3(wild2, wild2))          [1 0 0 [wild1:5] [wild2:5] ]
/// ```
///
/// If variants share a prefix encoding that includes wildcards, then the
/// subsequent variants must not use wildcard identifiers and numbers.
/// Instead they must use "_" for both. E.g.:
///
/// ```no_a_doc_test
/// (V1(wild1, wild2))   [0 1 1 [wild1:5] 0 0 0 [wild2:5] ]
/// (V2(wild1, wild2))   [0 1 1 [_:_]     0 0 1 [wild1:2] [wild2:3] ]
/// ```
///
/// A group is a set of "0" or "1" inside "[]". They can appear in the same
/// pattern position as a wildcard does in another variant. When the decoding
/// reaches a position with groups and 1 wildcard, it tries to decode the groups
/// first as if the "[]" weren't there. If a variant's group succeeds, that
/// variant is chosen for further decoding. If no groups succeed, the variant
/// with the wildcard is chosen. For encoding, the groups are treated as if "[]"
/// wasn't there.
///
/// In the following example, V1 is decoded 0b001 (2), V2 is decoded for 0b010
/// (4) and V3 otherwise.
///
/// ```no_a_doc_test
/// (V1)        [0 [0 1] ]      // 0b001
/// (V2)        [0 [1 0] ]      // 0b010
/// (V3(wild))  [0 [wild:2] ]   // 0b000 or 0b011
/// ```
///
/// Additionally, fixed encodings ("0" or "1") cannot clash with
/// wildcards/groups for a given bit. This means if a "0" or "1" is defined in
/// one variant for a specific bit, a wildcard/groups cannot be defined for
/// another variant's same bit:
///
/// ```no_a_doc_test
/// (V1(wild1, wild2))   [0 1 1 [wild1:5] 0 0 0 [wild2:5] ]
/// (V1(wild1, wild2))   [0 1 1 [_:_]     0 1 [wild1:2] [wild2:3] ]
/// // Error V1 has "0" but V2 has wildcard   ^^^^^^^^^
/// ```
///
/// The resulting encoder/decoder has the following functions:
///
/// ```no_a_doc_test
/// /// Create a new FSM instance for encoding the given variant.
/// /// Returns `None` if the given variant cannot be encoded by this FSM.
/// fn new_encode(to_enc: &v) -> Option<FSM>;
/// /// Decodes the given u16.
/// /// `starting_bit` designates the position in the u16 to start decoding from.
/// /// 0 signifies the most significant bit.
/// fn decode_from(source:u16, starting_bit: u32) -> FSM;
/// /// Encodes the FSM into the given u16.
/// /// `starting_bit` designates the lowest significance bit in the u16 to encode in.
/// /// The encoding is then done into that bit and those more significant.
/// fn encode_from(self, target: &mut u16, starting_bit: u32);
/// ```
macro_rules! impl_encoding {
    /*
     This macro works by stepwise "unwrapping" the given patterns and then
     producing the required states of the encoding/decoding fsm.

     First, the given patterns are wrapped in "[]" preceded by the implicit initial state "S"

     For every unwrap step, The first pattern position in each variant is extracted and the
     variants are sorted into their respective patterns. E.g. if the variant have fixed patterns
     They are sorted into two groups denoting "0" or "1".
     In each variant, its first "0" or "1" is removed, such that its pattern is not 1 shorter.
     In case of groups, variant gets its own sorted group. However, if they are all wildcards
     they go into a single group.

     Then comes the transition step (denoted by "@build_fsm").
     Given the unwrapping, fsm state names are created based on the pattern and added to
     the list of states. For "0" or "1" only 2 states are added. For only wildcards 1 state is added.
     For groups, we create a state for each group and the wildcard.
     Then we recursively call this macro, to create an fsm that decodes the groups into
     their respective states. In case of no groups successfully decoded, the recursive fsm
     produces the wildcard state.

     When we are finished with the transition. Each variant is wrapped in its respective state
     we just created (still without the sub-pattern we "unwrapped").
     We then unwrap them all again.

     When a variant has no more patterns left, the last state create for it is a final state
     that uniquely represent the variant.

     When we create a state for a wildcard, we take the previous state and add a memeber to
     it that contains the wildcard's decoded value. Variants with multiple wildcards will
     have final states with a member for each wildcard in-order.

     Almost every rules starts with the following "@" groups, each followed by a "[]" containing
     the following:

     @fsm: Fsm name, encoded enum name, invalid decoding expression  (as explained in the beginning
        of the documentation).

     @states: The non-final states of the fsm. Each is in a "[]" and has inside it:
        The identifier is given first in "[]". It my contain multiple strings, all of which
        are concatenated at the end using paste!.
        Thereafter comes "{}" containing the list of wildcards and their lengths that the
        state so far has decoded.
        When we create new states, we take the old states identifier "[]" and add "_" and
        the pattern to it. I.e. "_0" for 0, "_1" for 1, the wildcards identifier, and in case
        of groups, the whole group e.g. "_010" for [0 1 0].

     @transitions: The transitions of the fsm each inside "[]".
        For fixed-pattern transitions (1 or 0), they contain first the "source" state
        and then the "target" state as seen from when decoding. Then follows 0 or 1 to designate
        the pattern.
        For wildcards/groups, the wildcard follows instead of 0 or 1.
        If no groups are given, nothing follows the wildcard.

        For patterns with groups, the "target" state is just the state for decoding wildcards.
        Following the wildcard comes first a "[]" containing the name of recursive Fsm decoing
        the groups (to be concatenated later) and then follows a "[]" containing the names
        of all Fsm enum variants that represent each group (each in "[]" to be concatenated later).

     @finals: The final states of the fsm, much like @states.

     Depending on where in the macro we are the following "@" can be found:

     @unwrap: Designates that we are unwrapping patterns
        Is followed by 3 "[]":
        1. Contains unwrapped patterns and variant as described earlier.
        2. Contains the state currently being further unwrapped.
        3. Contains the variants and patterns that have yet to be unwrapped. When this is empty
            the unwrapping is done for this state.


     @build_fsm: Designates we are building the fsm after unwrapping.
        Is followed by 2 "[]":
        1. The state "source" state of a decoding.
        2. A list of patters (0, 1, wildcard or group) followed by "[]" containing
            variants and their further patterns.

    */
    (
        @init $fsm:tt
        $(
            $variant:tt $pattern:tt
        )+
    )=>{
        impl_encoding!{
            @fsm $fsm
            @states [ [[S] {}] ]
            @transitions []
            @finals []
            @unwrap
            []
            [[S] {}] [ $($variant $pattern)+ ]
        }
    };

    (
        // The beginning of a new unwrap step
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        []
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ $pat1:tt $($pattern:tt)* ]
            $(
                $variant_rest:tt $pattern_rest:tt
            )*
        ]
        $($rest:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @unwrap
            [$pat1 [ $variant [$($pattern)*] ]]
            [[$($from)+] $from_args] [
                $(
                    $variant_rest $pattern_rest
                )*
            ]
            $($rest)*
        }
    };

    (
        // Unwrap 0
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            0 [ $($unwrapped_0:tt)+ ]
            $(1 [ $($unwrapped_1:tt)+ ])?
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ 0 $($pattern:tt)* ]
            $(
                $variant_rest:tt $pattern_rest:tt
            )*
        ]
        $($rest:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @unwrap
            [
                0 [ $($unwrapped_0)+ $variant [$($pattern)*]]
                $(1 [ $($unwrapped_1)+ ])?
            ]
            [[$($from)+] $from_args] [
                $(
                    $variant_rest $pattern_rest
                )*
            ]
            $($rest)*
        }
    };

    (
        // Unwrap 0 first time after 1
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            1 [ $($unwrapped_1:tt)+ ]
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ 0 $($pattern:tt)* ]
            $(
                $variant_rest:tt $pattern_rest:tt
            )*
        ]
        $($rest:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @unwrap
            [
                0 [ $variant [$($pattern)*]]
                1 [ $($unwrapped_1)+ ]
            ]
            [[$($from)+] $from_args] [
                $(
                    $variant_rest $pattern_rest
                )*
            ]
            $($rest)*
        }
    };

    (
        // Unwrap 1
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            $(0 [ $($unwrapped_0:tt)+ ])?
            1 [ $($unwrapped_1:tt)+ ]
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ 1 $($pattern:tt)* ]
            $(
                $variant_rest:tt $pattern_rest:tt
            )*
        ]
        $($rest:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @unwrap
            [
                $(0 [ $($unwrapped_0)+])?
                1 [ $($unwrapped_1)+ $variant [$($pattern)*]]
            ]
            [[$($from)+] $from_args] [
                $(
                    $variant_rest $pattern_rest
                )*
            ]
            $($rest)*
        }
    };

    (
        // Unwrap 1 first time
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            $(0 [ $($unwrapped_0:tt)+ ])?
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ 1 $($pattern:tt)* ]
            $(
                $variant_rest:tt $pattern_rest:tt
            )*
        ]
        $($rest:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @unwrap
            [
                $(0 [ $($unwrapped_0)+ ])?
                1 [ $variant [$($pattern)*]]
            ]
            [[$($from)+] $from_args] [
                $(
                    $variant_rest $pattern_rest
                )*
            ]
            $($rest)*
        }
    };

    (
        // Unwrap wildcard after first time.
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            [$unwrapped_id:ident:$unwrapped_size:literal] [ $($unwrapped:tt)+ ]
            $(
                [$($group_rest:tt)*][ $($unwrapped_rest:tt)+ ]
            )*
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ [ _: _ ] $($pattern:tt)* ]
            $(
                $variant_rest:tt $pattern_rest:tt
            )*
        ]
        $($rest:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @unwrap
            [
                [$unwrapped_id :$unwrapped_size] [ $($unwrapped)+ $variant [$($pattern)*] ]
                $(
                    [$($group_rest)*][ $($unwrapped_rest)+ ]
                )*
            ]
            [[$($from)+] $from_args] [
                $(
                    $variant_rest $pattern_rest
                )*
            ]
            $($rest)*
        }
    };

    (
        // Unwrap wildcard first time after groups.
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            $(
                [$($group_rest:tt)*][ $($unwrapped_rest:tt)+ ]
            )+
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ [ $id:ident:$size:literal ] $($pattern:tt)* ]
            $(
                $variant_rest:tt $pattern_rest:tt
            )*
        ]
        $($rest:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @unwrap
            [
                [$id :$size] [ $variant [$($pattern)*] ]
                $(
                    [$($group_rest)*][ $($unwrapped_rest)+ ]
                )+
            ]
            [[$($from)+] $from_args] [
                $(
                    $variant_rest $pattern_rest
                )*
            ]
            $($rest)*
        }
    };

    (
        // Unwrap group.
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            $($unwrapped:tt)*
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ [ $($group:tt)+ ] $($pattern:tt)* ]
            $(
                $variant_rest:tt $pattern_rest:tt
            )*
        ]
        $($rest:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @unwrap
            [
                $($unwrapped)*
                [$($group)+] [ $variant [$($pattern)*] ]
            ]
            [[$($from)+] $from_args] [
                $(
                    $variant_rest $pattern_rest
                )*
            ]
            $($rest)*
        }
    };

    (
        // Disallow a wildcard pattern alongside fixed patterns (0 or 1)
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            $(0)? $(1)? [ $($unwrapped_0:tt)+ ]
            $(1 [ $($unwrapped_1:tt)+ ])?
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ [$_id:ident:$_size:literal] $($pattern:tt)* ]
           $($patterns_rest:tt)*
        ]
        $($rest:tt)*
    ) => {
        compile_error!{"Wildcard pattern alongside fixed pattern (0 or 1)"}
    };

    (
        // Disallow a wildcard pattern after another wildcard pattern
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            [$unwrapped_id:ident : $unwrapped_size:literal] [ $($unwrapped:tt)+ ]
            $($group_rest:tt)*
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ [$_id:ident:$_size:literal] $($pattern:tt)* ]
           $($patterns_rest:tt)*
        ]
        $($rest:tt)*
    ) => {
        compile_error!{"Wildcard pattern alongside another wildcard pattern"}
    };

    (
        // Disallow a 0 pattern alongside wildcard patterns
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            [$unwrapped_id:ident : $unwrapped_size:literal] [ $($unwrapped:tt)+ ]
            $($group_rest:tt)*
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ 0 $($pattern:tt)* ]
           $($patterns_rest:tt)*
        ]
        $($rest:tt)*
    ) => {
        compile_error!{"Fixed pattern (0) alongside wildcard pattern"}
    };

    (
        // Disallow a 1 pattern alongside wildcard patterns
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [
            [$unwrapped_id:ident : $unwrapped_size:literal] [ $($unwrapped:tt)+ ]
            $($group_rest:tt)*
        ]
        [[$($from:tt)+] $from_args:tt] [
            $variant:tt [ 1 $($pattern:tt)* ]
           $($patterns_rest:tt)*
        ]
        $($rest:tt)*
    ) => {
        compile_error!{"Fixed pattern (1) alongside wildcard pattern"}
    };

    (
        // End of unwrap step
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @unwrap
        [ $($pattern:tt [$($pattern__rest:tt)*])+ ]
        [[$($from:tt)+] $from_args:tt] []
        $($rest:tt)*

    ) => {
        impl_encoding!{
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @build_fsm
            [[$($from)+] $from_args] [
                $($pattern [$($pattern__rest)*])+
            ]
            $($rest)*
        }
    };

    (
        // Remove empty
        @fsm $fsm:tt
        @states $states:tt
        @transitions [ $($trans:tt)* ]
        @finals [ $($final:tt)* ]
        @build_fsm
        [[$($from:tt)+] $from_args:tt] []
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @fsm $fsm
            @states $states
            @transitions [ $($trans)* ]
            @finals [ $($final)* ]
            $($rest)*
        }
    };

    (
        // Transition using 0 pattern to final
        @fsm $fsm:tt
        @states $states:tt
        @transitions [ $($transitions_rest:tt)* ]
        @finals [ $($final:tt)* ]
        @build_fsm
        [[$($from:tt)+] $from_args:tt] [ 0 [ $variant:tt [] ] $($rest_patterns:tt)* ]
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @fsm $fsm
            @states $states
            @transitions [
                $($transitions_rest)*
                [[[$($from)+] $from_args] [[$($from)+ _ 0] $from_args] 0]
            ]
            @finals [ $($final)* [[$($from)+ _ 0] $from_args : $variant] ]
            @build_fsm
            [[$($from)+] $from_args] [  $($rest_patterns)* ]
            $($rest)*
        }
    };

    (
        // Transition using 0 pattern
        @fsm $fsm:tt
        @states [ $($states_rest:tt)* ]
        @transitions [ $($transitions_rest:tt)* ]
        @finals [ $($final:tt)* ]
        @build_fsm
        [[$($from:tt)+] $from_args:tt] [ 0 [ $($embedded_patterns:tt)+ ] $($rest_patterns:tt)* ]
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @fsm $fsm
            @states [ $($states_rest)* [[$($from)+ _0] $from_args] ]
            @transitions [
                $($transitions_rest)*
                [[[$($from)+] $from_args] [[$($from)+ _0] $from_args] 0]
            ]
            @finals [ $($final)* ]
            @build_fsm
            [[$($from)+] $from_args] [  $($rest_patterns)* ]
            $($rest)*
            @unwrap
            []
            [[$($from)+ _0] $from_args] [ $($embedded_patterns)+ ]
        }
    };

    (
        // Transition using 1 pattern to final
        @fsm $fsm:tt
        @states $states:tt
        @transitions [ $($transitions_rest:tt)* ]
        @finals [ $($finals:tt)* ]
        @build_fsm
        [[$($from:tt)+] $from_args:tt] [ 1 [ $variant:tt [] ] $($rest_patterns:tt)* ]
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @fsm $fsm
            @states $states
            @transitions [
                $($transitions_rest)*
                [[[$($from)+] $from_args] [[$($from)+ _1] $from_args] 1]
            ]
            @finals [ $($finals)* [[$($from)+ _1] $from_args : $variant] ]
            @build_fsm
            [[$($from)+] $from_args] [  $($rest_patterns)* ]
            $($rest)*
        }
    };

    (
        // Transition using 1 pattern
        @fsm $fsm:tt
        @states [ $($states_rest:tt)* ]
        @transitions [ $($transitions_rest:tt)* ]
        @finals [ $($final:tt)* ]
        @build_fsm
        [[$($from:tt)+] $from_args:tt] [ 1 [ $($embedded_patterns:tt)+ ] $($rest_patterns:tt)* ]
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @fsm $fsm
            @states [ $($states_rest)* [[$($from)+ _1] $from_args] ]
            @transitions [
                $($transitions_rest)*
                [[[$($from)+] $from_args] [[$($from)+ _1] $from_args] 1]
            ]
            @finals [ $($final)* ]
            @build_fsm
            [[$($from)+] $from_args] [  $($rest_patterns)* ]
            $($rest)*
            @unwrap
            []
            [[$($from)+ _1] $from_args] [ $($embedded_patterns)+ ]
        }
    };

    (
        // Transition using only wildcard pattern to final
        @fsm $fsm:tt
        @states $states:tt
        @transitions [ $($transitions_rest:tt)* ]
        @finals [ $($final_rest:tt)* ]
        @build_fsm
        [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}] [
            [$wildcard_id:ident : $wildcard_size:literal] [ $variant:tt [] ]
        ]
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @fsm $fsm
            @states $states
            @transitions [
                $($transitions_rest)*
                [
                    [[$($from)+] {$($from_args_id : $from_args_size,)*}]
                    [   [$($from)+ _ $wildcard_id]
                        {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,}
                    ]
                    [$wildcard_id : $wildcard_size]
                ]
            ]
            @finals [
                $($final_rest)*
                [   [$($from)+ _ $wildcard_id]
                    {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,} :
                    $variant
                ]
            ]
            $($rest)*
        }
    };

    (
        // Transition using only wildcard pattern
        @fsm $fsm:tt
        @states [ $($states_rest:tt)* ]
        @transitions [ $($transitions_rest:tt)* ]
        @finals $finals:tt
        @build_fsm
        [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}] [
            [$wildcard_id:ident : $wildcard_size:literal] [ $($embedded_patterns:tt)+ ]
        ]
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @fsm $fsm
            @states [
                $($states_rest)*
                [   [$($from)+ _ $wildcard_id]
                    {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,}
                ]
            ]
            @transitions [
                $($transitions_rest)*
                [
                    [[$($from)+] {$($from_args_id : $from_args_size,)*}]
                    [   [$($from)+ _ $wildcard_id]
                        {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,}
                    ]
                    [$wildcard_id : $wildcard_size]
                ]
            ]
            @finals $finals
            $($rest)*
            @unwrap
            []
            [   [$($from)+ _ $wildcard_id]
                {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,}
            ] [ $($embedded_patterns)+ ]
        }
    };

    (
        // Transition using wildcard pattern with groups
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @build_fsm
        [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}] [
            [$wildcard_id:ident : $wildcard_size:literal] [ $($embedded_patterns:tt)+ ]
            $([$($group_pattern:literal)+][$($group_embedded_pat:tt)+])+
        ]
        $($rest:tt)*
    ) => {
		/*
		We create a state name for each group by concatenating $from and $group_pattern.
		However, we cannot do this in a single step as follows:
		$([ [$($from)+ _ $($group_pattern)+]
            {$($from_args_id : $from_args_size,)*}
        ])+
        since we will get an error about $from and $group_pattern not having the same repetitions
        Instead, we will expand each state name on its own, and in the end produce the final
        expansion
		 */
        impl_encoding! {
            @expand_group_states []
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @build_fsm
            [[$($from)+] {$($from_args_id : $from_args_size,)*}] [
                [$wildcard_id : $wildcard_size] [ $($embedded_patterns)+ ]
                $([$($group_pattern)+][$($group_embedded_pat)+])+
            ]
            $($rest)*
        }
	};

    (
        @expand_group_states [$($expanded:tt)*]
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @build_fsm
        [[$($from:tt)+] $from_args:tt] [
            [$wildcard_id:ident : $wildcard_size:literal] [ $($embedded_patterns:tt)+ ]
            [$($group_pattern:literal)+][$($group_embedded_pat:tt)+]
            $($group_rest:tt)*
        ]
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @expand_group_states [
                $($expanded)*
                [
                    [$($from)+ _ $($group_pattern)+] // State name
                    $from_args // State args
                    [$($group_pattern)+]
                    [$($group_embedded_pat)+]
                ]
            ]
            @fsm $fsm
            @states $states
            @transitions $transitions
            @finals $finals
            @build_fsm
            [[$($from)+] $from_args] [
                [$wildcard_id : $wildcard_size] [ $($embedded_patterns)+ ]
                $($group_rest)*
            ]
            $($rest)*
        }
	};

    (
        // Finished expanding group state names. Transition to final
        @expand_group_states [
            $([
                [$($group_state_name:tt)+]
                {$($group_state_args_id:ident : $group_state_args_size:literal,)*}
                [$($group_pattern:literal)+]
                [$group_variant:tt []]
            ])+
        ]
        @fsm [$fsm_name:ident $($fsm_rest:tt)*]
        @states [ $($states_rest:tt)* ]
        @transitions [ $($transitions_rest:tt)* ]
        @finals [ $($final_rest:tt)* ]
        @build_fsm
        [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}] [
            [$wildcard_id:ident : $wildcard_size:literal] [ $variant:tt [] ]
        ]
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @fsm [$fsm_name $($fsm_rest)*]
            @states [
                $($states_rest)*
                [
                    [ $($from)+ _ $fsm_name _Invalid]{}
                ]
            ]
            @transitions [
                $($transitions_rest)*
                [
                    [[$($from)+] {$($from_args_id : $from_args_size,)*}]
                    [   [$($from)+ _ $wildcard_id]
                        {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,}
                    ]
                    [$wildcard_id : $wildcard_size]
                    [ $fsm_name _ $($from)+ ]
                    [ $([$($group_state_name)+])+ ]
                ]
            ]
            @finals [
                $($final_rest)*
                [   [$($from)+ _ $wildcard_id]
                    {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,} :
                    $variant
                ]
                $([ [$($group_state_name)+]
                    {$($group_state_args_id : $group_state_args_size,)* } :
                    $group_variant
                ])+
            ]
            $($rest)*
        }
        paste::paste!{
        impl_encoding!{
            // #1 fsm name #2 name of decoded type #3 variant (in decoded type) to use upon failure
            // #4 which bit (0=most significant) to start decoding from
            @init [[< $fsm_name _ $($from)+>] $fsm_name (|_|[< $($from)+ _ $fsm_name _Invalid>]{})]
            $(([< $($group_state_name)+ >]())[$($group_pattern)+])+
        }}
    };

    (
        // Finished expanding group state names. Transition
        @expand_group_states [
            $([
                [$($group_state_name:tt)+]
                {$($group_state_args_id:ident : $group_state_args_size:literal,)*}
                [$($group_pattern:literal)+]
                [$($group_embedded_pat:tt)+]
            ])+
        ]
        @fsm [$fsm_name:ident $($fsm_rest:tt)*]
        @states [ $($states_rest:tt)* ]
        @transitions [ $($transitions_rest:tt)* ]
        @finals $finals:tt
        @build_fsm
        [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}] [
            [$wildcard_id:ident : $wildcard_size:literal] [ $($embedded_patterns:tt)+ ]
        ]
        $($rest:tt)*
    ) => {
        impl_encoding! {
            @fsm [$fsm_name $($fsm_rest)*]
            @states [
                $($states_rest)*
                [   [$($from)+ _ $wildcard_id]
                    {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,}
                ]
                $([ [$($group_state_name)+]
                    {$($group_state_args_id : $group_state_args_size,)*}
                ])+
                [
                    [ $($from)+ _ $fsm_name _Invalid]{}
                ]
            ]
            @transitions [
                $($transitions_rest)*
                [
                    [[$($from)+] {$($from_args_id : $from_args_size,)*}]
                    [   [$($from)+ _ $wildcard_id]
                        {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,}
                    ]
                    [$wildcard_id : $wildcard_size]
                    [ $fsm_name _ $($from)+ ]
                    [ $([$($group_state_name)+])+ ]
                ]
            ]
            @finals $finals
            $($rest)*
            @unwrap
            []
            [   [$($from)+ _ $wildcard_id]
                {$($from_args_id : $from_args_size,)* $wildcard_id : $wildcard_size,}
            ] [ $($embedded_patterns)+ ]
            $(
                @unwrap
                []
                [   [$($group_state_name)+]
                    {$($group_state_args_id : $group_state_args_size,)*}
                ] [ $($group_embedded_pat)+ ]
            )+
        }
        paste::paste!{
        impl_encoding!{
            // #1 fsm name #2 name of decoded type #3 variant (in decoded type) to use upon failure
            // #4 which bit (0=most significant) to start decoding from
            @init [[< $fsm_name _ $($from)+>] $fsm_name (|_|[< $($from)+ _ $fsm_name _Invalid>]{})]
            $(([< $($group_state_name)+ >]())[$($group_pattern)+])+
        }}
    };

    (
        // Disallow groups without a wildcard associated
        @fsm $fsm:tt
        @states $states:tt
        @transitions $transitions:tt
        @finals $finals:tt
        @build_fsm
        [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}] [
            $([$($group_pattern:literal)+][$($group_embedded_pat:tt)+])+
        ]
        $($rest:tt)*
    ) => {
        compile_error!{"Cannot have group pattern ([0 1 ...]) without wildcard pattern"}
    };

    (
        // Finished FSM building
        @fsm [$fsm_name:ident $encoded_name:ident $failed_decode:expr]
        @states [ [[$init_state:tt]  {}] $([[$($state_id:tt)+] {$($state_args_id:ident : $state_args_size:literal,)*}])+ ]
        @transitions $transitions:tt
        @finals [ $([ [$($final_id:tt)+] {$($final_args_id:ident : $final_args_size:literal,)*} : ($variant:pat) ])+ ]
    ) => {
        paste::paste!{
            #[allow(non_camel_case_types)]
            pub enum $fsm_name {
                $init_state(),
                $(
                    [< $($state_id)+ >] ($(Bits<$state_args_size, false>,)*),
                )+
                $(
                    [< $($final_id)+ >] ($(Bits<$final_args_size, false>,)*),
                )+
                /// If during decoding a transition cannot find a pattern to match
                /// the current bit, this state is produced with the contents of the
                /// u16 being decoded.
                FailedDecoding(u16)
            }

            impl $fsm_name {
                fn new_decode() -> Self {
                    $fsm_name::$init_state()
                }

                fn new_encode(to_enc: &$encoded_name) -> Option<Self> {
                    use $fsm_name::*;
                    #[allow(unused_variables)]
                    match to_enc {
                        $(
                            $encoded_name::$variant =>
                                Some([< $($final_id)+ >] ($(std::convert::Into::into(*$final_args_id),)*)),
                        )+
                        _ => None
                    }
                }

                fn is_initial(&self) -> bool
                {
                    if let $fsm_name::$init_state() = self{ true } else { false }
                }

                fn is_final(&self) -> Option<$encoded_name>
                {
                    use $fsm_name::*;
                    #[allow(unused_variables)]
                    match self {
                        $init_state() => None,
                        $(
                            [< $($state_id)+ >]($($state_args_id,)*) => None,
                        )+

                        $(
                            [< $($final_id)+ >] ($($final_args_id,)*) =>
                            {
                                $(let $final_args_id = std::convert::Into::into(*$final_args_id);)*
                                Some($encoded_name::$variant)
                            }
                        )+
                        FailedDecoding(code) => {
                            use $encoded_name::*;
                            Some($failed_decode(*code))
                        }
                    }
                }

                fn decode_transition(self, code: u16, done: u32) -> (Self, u32)
                {
                    assert!(done < 16);
                    assert!(self.is_final().is_none());

                    #[allow(unused_variables)]
                    let extract = |size:u32| {
                        let mut mask = u16::MAX;
                        mask = mask << done;
                        mask = mask >> 16-size;
                        mask = mask << (16-size-done);
                        ((code & mask) >> (16-size-done)) as i32
                    };

                    impl_encoding!{
                        @fsm [$fsm_name $encoded_name ]
                        @finalize_decode [self code done extract]
                        @transitions $transitions
                    }
                }

                fn encode_transition(self, into: &mut u16, done:u32) -> (Self, u32)
                {
                    assert!(done < 16);
                    assert!(!self.is_initial());

                    impl_encoding!{
                        @fsm [$fsm_name $encoded_name ]
                        @finalize_encode [self into done]
                        @transitions $transitions
                    }
                }

                /// The starting bit goes from highest to lowest significance
                fn decode_from(code:u16, starting_bit: u32) -> $encoded_name
                {
                    let mut decoder = $fsm_name::new_decode();
                    let mut done = starting_bit;
                    while decoder.is_final().is_none()
                    {
                        let result = decoder.decode_transition(code, done);
                        decoder = result.0;
                        done = result.1;
                    }
                    decoder.is_final().unwrap()
                }

                /// The starting bit goes from lowest to highest significance
                fn encode_from(self, into: &mut u16, starting_bit: u32)
                {
                    let mut encoder = self;
                    let mut done = starting_bit;
                    while !encoder.is_initial()
                    {
                        let result = encoder.encode_transition(into, done);
                        encoder = result.0;
                        done = result.1;
                    }
                }
            }
        }
    };

    (
        @fsm $fsm:tt
        @finalize_decode [$_self:ident $variant:ident $done:ident $extract:ident]
        @transitions [
            [
                [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}]
                [[$($to:tt)+] {$($to_args_id:ident : $to_args_size:literal,)*}]
                [$wildcard_id:ident : $wildcard_size:literal]
            ]
            $($rest_trans:tt)*
        ]
        $($finalized_transitions:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @finalize_decode [$_self $variant $done $extract]
            @transitions [$($rest_trans)*]
            $($finalized_transitions)*
            [< $($from)+ >]($($from_args_id,)*) => {
                let extracted = (
                    $extract(<Bits<$wildcard_size, false>>::SIZE)
                ).try_into().unwrap();
                (   [< $($to)+ >]($($from_args_id,)* extracted ),
                    $done + <Bits<$wildcard_size, false>>::SIZE
                )
            }
        }
    };

    (
        @fsm $fsm:tt
        @finalize_encode [$_self:ident $variant:ident $done:ident]
        @transitions [
            [
                [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}]
                [[$($to:tt)+] {$($to_args_id:ident : $to_args_size:literal,)*}]
                [$wildcard_id:ident : $wildcard_size:literal]
                $(
                    [$($group_fsm_name:tt)+]
                    [] // group encodings have already been handled.
                )?
            ]
            $($rest_trans:tt)*
        ]
        $($finalized_transitions:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @finalize_encode [$_self $variant $done]
            @transitions [$($rest_trans)*]
            $($finalized_transitions)*

            [< $($to)+ >]($($from_args_id,)* last) => {
                let mut val = last.value as u16;
                val <<= $done;
                *$variant |= val;
                ([< $($from)+ >]($($from_args_id,)*), $done + <Bits<$wildcard_size, false>>::SIZE)
            }
        }
    };

    (
        @fsm [$fsm_name:ident $($fsm_rest:tt)*]
        @finalize_decode [$_self:ident $variant:ident $done:ident $extract:ident]
        @transitions [
            [
                [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}]
                [[$($to:tt)+] {$($to_args_id:ident : $to_args_size:literal,)*}]
                [$wildcard_id:ident : $wildcard_size:literal]
                [$($group_fsm_name:tt)+]
                $group_state_names:tt
            ]
            $($rest_trans:tt)*
        ]
        $($finalized_transitions:tt)*
    ) => {
        impl_encoding!{
            @fsm [$fsm_name $($fsm_rest)*]
            @finalize_decode [$_self $variant $done $extract]
            @transitions [$($rest_trans)*]
            $($finalized_transitions)*
            [< $($from)+ >]($($from_args_id,)*) => {
                let fsm_result = [< $($group_fsm_name)+ >]::decode_from($variant, $done);

                (
                    if let [< $($from)+ _ $fsm_name _Invalid >]{} = fsm_result
                    {
                        let extracted = (
                            $extract(<Bits<$wildcard_size, false>>::SIZE)
                        ).try_into().unwrap();
                        [< $($to)+ >]($($from_args_id,)* extracted )
                    } else {
                        fsm_result
                    },
                    $done + <Bits<$wildcard_size, false>>::SIZE
                )
            }
        }
    };

    (
        @fsm [$fsm_name:ident $($fsm_rest:tt)*]
        @finalize_encode [$_self:ident $variant:ident $done:ident]
        @transitions [
            [
                [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}]
                [[$($to:tt)+] {$($to_args_id:ident : $to_args_size:literal,)*}]
                [$wildcard_id:ident : $wildcard_size:literal]
                [$($group_fsm_name:tt)+]
                [
                    [$($group_state_name:tt)+]
                    $([$($group_state_name_rest:tt)+])*
                ]
            ]
            $($rest_trans:tt)*
        ]
        $($finalized_transitions:tt)*
    ) => {
        impl_encoding!{
            @fsm [$fsm_name $($fsm_rest)*]
            @finalize_encode [$_self $variant $done ]
            @transitions [
                [
                    [[$($from)+] {$($from_args_id : $from_args_size,)*}]
                    [[$($to)+] {$($to_args_id : $to_args_size,)*}]
                    [$wildcard_id : $wildcard_size]
                    [$($group_fsm_name)+]
                    [$([$($group_state_name_rest)+])*]
                ]
                $($rest_trans)*
            ]
            $($finalized_transitions)*
            [<$($group_state_name)+>]($($from_args_id,)*) => {
                // We transform the state into the wildcard state with the wildcard
                // containing the pattern of this state.
                // The resulting state is then treated as a wildcard, which simply encodes
                // the value we set here.
                let group_encoder = [< $($group_fsm_name)+ >]::
                    new_encode(&[<$($group_state_name)+>]($($from_args_id,)*)).unwrap();
                let mut group_enc = 0;
                group_encoder.encode_from(&mut group_enc, 0);
                let group_wild = (group_enc as i32).try_into().unwrap();
                ([< $($to)+ >]($($from_args_id,)* group_wild), $done)
            }
        }
    };

    (
        @fsm $fsm:tt
        @finalize_decode [$_self:ident $variant:ident $done:ident $extract:ident]
        @transitions [
            [
                [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}]
                [[$($to:tt)+] {$($to_args_id:ident : $to_args_size:literal,)*}]
                0
            ]
            $($rest_trans:tt)*
        ]
        $($finalized_transitions:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @finalize_decode [$_self $variant $done $extract]
            @transitions [$($rest_trans)*]
            $($finalized_transitions)*
            [< $($from)+ >]($($from_args_id,)*) if ((1 << (15-$done)) & $variant) == 0 =>
            ([< $($to)+ >]($($from_args_id,)*), $done + 1),
        }
    };

    (
        @fsm $fsm:tt
        @finalize_encode [$_self:ident $variant:ident $done:ident]
        @transitions [
            [
                [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}]
                [[$($to:tt)+] {$($to_args_id:ident : $to_args_size:literal,)*}]
                0
            ]
            $($rest_trans:tt)*
        ]
        $($finalized_transitions:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @finalize_encode [$_self $variant $done]
            @transitions [$($rest_trans)*]
            $($finalized_transitions)*
            [< $($to)+ >]($($to_args_id,)*) => {
                let mask = !(1 << $done);
                *$variant &= mask; // Clear the bit
                ([< $($from)+ >]($($from_args_id,)*), $done + 1)
            }
        }
    };

    (
        @fsm $fsm:tt
        @finalize_decode [$_self:ident $variant:ident $done:ident $extract:ident]
        @transitions [
            [
                [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}]
                [[$($to:tt)+] {$($to_args_id:ident : $to_args_size:literal,)*}]
                1
            ]
            $($rest_trans:tt)*
        ]
        $($finalized_transitions:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @finalize_decode [$_self $variant $done $extract]
            @transitions [$($rest_trans)*]
            $($finalized_transitions)*
            [< $($from)+ >]($($from_args_id,)*) if ((1 << (15-$done)) & $variant) > 0 =>
            ([< $($to)+ >]($($from_args_id,)*), $done + 1),
        }
    };

    (
        @fsm $fsm:tt
        @finalize_encode [$_self:ident $variant:ident $done:ident]
        @transitions [
            [
                [[$($from:tt)+] {$($from_args_id:ident : $from_args_size:literal,)*}]
                [[$($to:tt)+] {$($to_args_id:ident : $to_args_size:literal,)*}]
                1
            ]
            $($rest_trans:tt)*
        ]
        $($finalized_transitions:tt)*
    ) => {
        impl_encoding!{
            @fsm $fsm
            @finalize_encode [$_self $variant $done]
            @transitions [$($rest_trans)*]
            $($finalized_transitions)*
            [< $($to)+ >]($($to_args_id,)*) => {
                let mask = 1 << $done;
                *$variant |= mask; // set the bit
                ([< $($from)+ >]($($from_args_id,)*), $done + 1)
            }
        }
    };

    (
        @fsm [$fsm_name:ident $($fms_rest:tt)*]
        @finalize_decode [$_self:ident $variant:ident $done:ident $extract:ident]
        @transitions []
        $($finalized_transitions:tt)*
    ) => {
        use $fsm_name::*;
        paste::paste!{
            match $_self {
                $($finalized_transitions)*
                _ => (FailedDecoding($variant), $done)
            }
        }
    };

    (
        @fsm [$fsm_name:ident $($fms_rest:tt)*]
        @finalize_encode [$_self:ident $variant:ident $done:ident]
        @transitions []
        $($finalized_transitions:tt)*
    ) => {
        use $fsm_name::*;
        paste::paste!{
            match $_self {
                $($finalized_transitions)*
                 _ => unreachable!("All states should be handled except invalid states, \
                    which shouldn't be reachable")
            }
        }
    };
}

map_mnemonics! {
	"jmp"(Jump(imm, loc)) [ 0 1 1 [imm:7] [loc:6] ]
	{
		(imm, loc) <= Or<
			JumpOffsets,
			Offset<13,false>,
			_
		>
		=> (*imm, *loc)
	}
	"ret"(Call(CallVariant::Ret, loc)) [ 0 0 0 1 0 0 0 0 0 0 [loc:6]]
	{
		loc = Offset<6,false>
	}
	"cap" (Capture(tar1,tar2)) [ 0 1 0 0 0 1 [tar1:5] [tar2:5]]
	{
		(tar1,tar2) <= CommaBetween<
			ReferenceParser<5>,
			ReferenceParser<5>,
		> => (*tar1,*tar2)
	}
	"dup" (Duplicate(next, tar1,tar2)) [ 1 0 1 1 1 [next:1] [tar1:5] [tar2:5]]
	{
		(tar1,(tar2,next)) <= CommaBetween<
			ReferenceParser<5>,
			Then<
				ReferenceParser<5>,
				BoolFlag<Then<Comma, Alone<Arrow>>>
			>,
		> => (*tar1,(*tar2,*next))
	}
	"echo" (Echo(next,tar1,tar2)) [ 1 0 1 1 0 [next:1] [tar1:5] [tar2:5]]
	{
		(tar1,(tar2,next)) <= CommaBetween<
			ReferenceParser<5>,
			Then<
				ReferenceParser<5>,
				BoolFlag<Then<Comma, Alone<Arrow>>>
			>,
		> => (*tar1,(*tar2,*next))
	}
	(EchoLong(target)) [ 0 1 0 0 0 0 [target:10] ]
	{
		target = ReferenceParser<10>
	}
	"inc"(Alu(AluVariant::Inc, target))             [ 1 0 0 0 0 0 0 0 [0 0 0]       [target:5]]
	"dec"(Alu(AluVariant::Dec, target))             [ 1 0 0 0 0 0 0 1 [0 0 0]       [target:5]]
	"rol"(Alu(AluVariant::RotateLeft, target))      [ 1 0 0 0 0 0 1 0 [0 0 0]       [target:5]]
	"ror"(Alu(AluVariant::RotateRight, target))     [ 1 0 0 0 0 0 1 1 [0 0 0]       [target:5]]
	{
		target = ReferenceParser<5>
	}
	"add"
	(Alu(AluVariant::Add, target))                  [ 1 0 0 0 0 0 0 0 [1 1 1]       [target:5]]
	(Alu2(Alu2Variant::Add, output, target))        [ 1 0 0 0 0 0 0 0 [output:3]    [target:5]]
	"sub"
	(Alu(AluVariant::Sub, target))                  [ 1 0 0 0 0 0 0 1 [1 1 1]       [target:5]]
	(Alu2(Alu2Variant::Sub, output, target))        [ 1 0 0 0 0 0 0 1 [output:3]    [target:5]]
	"shl"
	(Alu(AluVariant::ShiftLeft, target))            [ 1 0 0 0 0 0 1 0 [1 1 1]       [target:5]]
	(Alu2(Alu2Variant::ShiftLeft, output, target))  [ 1 0 0 0 0 0 1 0 [output:3]    [target:5]]
	"shr"
	(Alu(AluVariant::ShiftRight, target))           [ 1 0 0 0 0 0 1 1 [1 1 1]       [target:5]]
	{
		target = ReferenceParser<5>
	}
	(Alu2(Alu2Variant::ShiftRight, output, target)) [ 1 0 0 0 0 0 1 1[output:3]     [target:5]]
	{
		(output, target) <= CommaBetween<
			Flatten<Then<
				Flag<High, Low>,
				Maybe<
					Then<Flag<Arrow, Plus>, Flag<High, Low>>
				>,
			>, _>,
			ReferenceParser<5>
		> => (*output, *target)
	}
	"pick" (Pick(target)) [ 0 1 0 1 0 0 0 0 0 0 0 [target:5] ]
	{
		target = ReferenceParser<5>
	}
	(PickI(imm, target)) [ 0 1 0 0 1 [imm:6] [target:5] ]
	{
		(imm, target) <= CommaBetween<
			Bits<6, false>,
			ReferenceParser<5>
		> => (*imm, *target)
	}
	"ld" (Load(signed, size, target)) [ 0 0 0 1 1 1 0 [signed:1] [size:3] [target:5] ]
	{
		((signed, size), target )<= CommaBetween<
			IntSize,
			ReferenceParser<5>
		> => ((*signed, *size), *target)
	}
	"st" (Store) [ 0 1 0 1 0 1 0 0 0 0 0 0 0 0 0 0 ]
	{
		() = ()
	}
	"nop" (Nop) [ 0 0 0 1 0 0 0 1 [0 0 0 0 0 0 0 0]]
	{
		() = ()
	}
	"req" (Request(v)) [ 0 0 0 1 0 0 0 1 [v:8]]
	{
		v <= Implicit<Exclude<Bits<8, false>,0>,255> => (*v)
	}
	"const"
	(Constant(imm)) [ 0 0 0 0 0 0 1 [imm:9] ]
	{
		imm <= TypedConst<8> => (*imm)
	}
}
