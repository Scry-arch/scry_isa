use std::collections::HashMap;
use lazy_static::lazy_static;
use crate::{matchers::*, instructions::*};

macro_rules! map_mnemonics {
    (
        $mnem1:literal( $($instr1:tt)* ) = {
            $parse_result1:tt <= $parser_type1:ty  => $print_as1:tt
        }
        $(
            $mnem:literal( $($instr:tt)* ) = {
                $parse_result:tt <= $parser_type:ty => $print_as:tt
            }
        )*
    ) => {
        map_mnemonics!{
            @indexify[
                [0]
                $mnem1 ( $($instr1)* ) = {
                    $parse_result1 <= $parser_type1 => $print_as1
                }
            ]
            [1]
            $(
                $mnem ( $($instr)* ) = {
                    $parse_result <= $parser_type => $print_as
                }
            )*
        }
    };
    
    (
        @indexify[$($prev:tt)*]
        [$idx:expr]
        $mnem1:literal( $($instr1:tt)* ) = {
            $parse_result1:tt <= $parser_type1:ty => $print_as1:tt
        }
        $(
            $mnem:literal( $($instr:tt)* ) = {
                $parse_result:tt <= $parser_type:ty => $print_as:tt
            }
        )*
    ) => {
        map_mnemonics!{
            @indexify[
                $($prev)*
                [$idx]
                $mnem1 ( $($instr1)* ) = {
                    $parse_result1 <= $parser_type1 => $print_as1
                }
            ]
            [$idx+1]
            $(
                $mnem ( $($instr)* ) = {
                    $parse_result <= $parser_type => $print_as
                }
            )*
        }
    };
    
    (
        @indexify[$($prev:tt)*]
        [$idx:expr]
    ) => {
        map_mnemonics!{
            $($prev)*
        }
    };
    
    (
        $(  [$idx:expr]
            $mnem:literal( $($instr:tt)* ) = {
                $parse_result:tt <= $parser_type:ty => $print_as:tt
            }
        )*
    ) => {
        const INSTRUCTION_MNEMONICS: &'static [&'static str] = &[
            $($mnem),*
        ];
        
        impl Instruction {
            pub fn mnemonic(&self) -> &'static str
            {
                use Instruction::*;
                #[allow(unused_variables)]
                match self {
                    $($($instr)* => INSTRUCTION_MNEMONICS[$idx],)*
                    _ => todo!(),
                }
            }
        }
        
        impl Parser for Instruction
        {
            type Internal = Instruction;
            
            fn parse<'a>(mut tokens: impl Iterator<Item=&'a str>  + Clone) -> Result<(Self::Internal, usize), usize>
            {
                use Instruction::*;
                lazy_static!{
                    static ref MNEMONIC_PARSERS: HashMap<&'static str, fn(&[&str]) -> std::result::Result<(Instruction, usize), usize>> = {
                        let mut mnem_pars:  HashMap<&'static str, fn(&[&str]) -> std::result::Result<(Instruction, usize), usize>>  = HashMap::new();
                        $(
                            mnem_pars.insert($mnem, {
                                fn parse(tokens: &[&str] ) -> Result<(Instruction, usize), usize>
                                {
                                    let ($parse_result, consumed) = <$parser_type>::parse(tokens.iter().cloned())?;
                                    Ok(($($instr)* , consumed))
                                }
                                parse
                            });
                        )*
                        mnem_pars
                    };
                }
                
                let mnemonic = tokens.next().ok_or_else(|| 0usize)?;
                if let Some(parser) = MNEMONIC_PARSERS.get(mnemonic) {
                    let tokens = tokens.collect::<Vec<_>>();
                    parser(tokens.as_ref()).map_or_else(|idx| Err(idx+1), |(instr, consumed)| Ok((instr, consumed+1)))
                }else {
                    Err(0)
                }
            }
            
            fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
            {
                use Instruction::*;
                
                out.write_str(Instruction::mnemonic(internal))?;
                out.write_str(" ")?;
                
                match internal {
                    $(
                        $($instr)* => {<$parser_type>::print(& $print_as, out )}
                    )*
                    _ => todo!()
                }
            }
        }
    };
}

map_mnemonics! {
    "jmp"(Jump(imm, loc)) = {
        (imm, loc) <= Or<
            CommaBetween<ReferenceParser<7,true>, ReferenceParser<6,false>>,
            ReferenceParser<13,false>
        >
        => (*imm, *loc)
    }
    "ret"(Call(CallVariant::Ret, loc)) = {
        loc <= ReferenceParser<6,false> => loc
    }
    "echo"(Echo(tar1,tar2,next)) = {
        (tar1,((),(tar2,next))) <= Then<
            ReferenceParser<5,false>,
            Then<
                Comma,
                Then<
                    ReferenceParser<5,false>,
                    BoolFlag<Then<Comma, Arrow>>
                >,
           >
        > => (*tar1,((),(*tar2,*next)))
    }
}