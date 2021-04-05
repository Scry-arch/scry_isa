use std::collections::HashMap;
use lazy_static::lazy_static;
use crate::{
    matchers::*,
    instructions::*
};

macro_rules! map_mnemonics {
    (
        $mnem1:literal( $($instr1:tt)* ) = {
            $parse_result1:tt = $parser_type1:ty
        }
        $(
            $mnem:literal( $($instr:tt)* ) = {
                $parse_result:tt = $parser_type:ty
            }
        )*
    ) => {
        map_mnemonics!{
            @indexify[
                0
                $mnem1 ( $($instr1)* ) = {
                    $parse_result1 = $parser_type1
                }
            ]
            [1]
            $(
                $mnem ( $($instr)* ) = {
                    $parse_result = $parser_type
                }
            )*
        }
    };
    
    (
        @indexify[$($prev:tt)*]
        [$idx:expr]
        $mnem1:literal( $($instr1:tt)* ) = {
            $parse_result1:tt = $parser_type1:ty
        }
        $(
            $mnem:literal( $($instr:tt)* ) = {
                $parse_result:tt = $parser_type:ty
            }
        )*
    ) => {
        map_mnemonics!{
            @indexify[
                $($prev)*
                $idx
                $mnem1 ( $($instr1)* ) = {
                    $parse_result1 = $parser_type1
                }
            ]
            [($idx+1)]
            $(
                $mnem ( $($instr)* ) = {
                    $parse_result = $parser_type
                }
            )*
        }
    };
    
    (
        @indexify[$($prev:tt)*]
        $idx:expr
    ) => {
        map_mnemonics!{
            $($prev)*
        }
    };
    
    (
        $(  $idx:literal
            $mnem:literal( $($instr:tt)* ) = {
                $parse_result:tt = $parser_type:ty
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
                        $($instr)* => {<$parser_type>::print(& map_mnemonics!{@refify $parse_result}, out)}
                    )*
                    _ => todo!()
                }
            }
        }
    };
    
    (@refify ( $($id:expr),* )) => {( $(*$id),* )};
    (@refify $id:expr) => {$id};
    
}

map_mnemonics! {
    "jmp"(Jump(imm, loc)) = {
        (imm, loc) = CommaBetween<ReferenceParser<7,true>, ReferenceParser<6,false>>
    }
    "ret"(Call(CallVariant::Ret, loc)) = {
        loc = ReferenceParser<6,false>
    }
}
