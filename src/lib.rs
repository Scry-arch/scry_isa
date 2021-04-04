//! This crate defines the Scry Instruction Set Architecture.

use duplicate::duplicate;
use std::collections::HashMap;
use lazy_static::lazy_static;

mod matchers;
pub use matchers::*;

/// Represents a set of N bits.
#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub struct Bits<const N: u32> {
    value: i32
}

impl<const N: u32> Bits<N> {
    
    #[duplicate(
        name max min value_type;
        [new_unsigned] [max_unsigned] [min_unsigned] [u16];
        [new_signed] [max_signed] [min_signed] [i16];
    
    )]
    /// Constructs a new Bits with given value.
    ///
    /// If the value isn't within a valid range None is returned.
    pub fn name(value: value_type) -> Option<Self> {
        if Self::max().value() >= value as i32 &&
            Self::min().value() <= value as i32 {
            Some(Self{value: value as i32})
        } else {
            None
        }
    }
    
    pub fn value(&self) -> i32 {
        self.value
    }
    
    pub fn saturated() -> Self {
        Self{value: ( 2i32.pow(N)) - 1}
    }
    
    pub fn cleared() -> Self {
        Self{value: 0}
    }
    
    pub fn max_unsigned() -> Self {
        Self::saturated()
    }
    
    pub fn min_unsigned() -> Self {
        Self::cleared()
    }
    
    pub fn max_signed() -> Self {
        Self{value: ( 2i32.pow(N)/2) - 1}
    }
    
    pub fn min_signed() -> Self {
        Self{value: ( 2i32.pow(N)/2) * -1}
    }
}

/// Variants of the call instruction
#[derive(Debug)]
pub enum CallVariant {
    Call, Portal, Ret, Trap
}

#[derive(Debug)]
pub enum StackControlVariant {
    Reserve, Free
}

/// All instructions
#[derive(Debug)]
pub enum Instruction {
    /// The jump instruction.
    ///
    /// Fields:
    /// 0. The branch target offset.
    /// 0. The branch location offset.
    Jump(Bits<7>,Bits<6>),
    
    /// load instruction.
    ///
    /// Fields
    /// 0. Whether the loaded value is signed.
    /// 0. The length of the loaded value.
    /// 0. The size of the loaded value.
    /// 0. Whether the primary address space is the target.
    /// 0. The "ar" flags.
    Load(bool, Bits<3>, Bits<3>,bool, Bits<2>),
    
    /// The echo instruction.
    ///
    /// Fields:
    /// 0. Output target 1.
    /// 0. Output target 2.
    /// 0. Whether the remaining inputs should be output to the the next instruction.
    Echo(Bits<5>, Bits<5>, bool),
    
    /// The ALU instruction.
    ///
    /// Fields:
    /// 0. Output target.
    /// 0. Function specifier.
    /// 0. Modifier.
    Alu(Bits<5>, Bits<4>, Bits<3>),
    
    /// The call instruction.
    ///
    /// Fields:
    /// 0. The variant.
    /// 0. The branch location offset.
    Call(CallVariant, Bits<6>),
    
    // The stack control instruction.
    //
    // First field is the variant.
    // Second field is whether the primary stack is the target.
    //     If false, the secondary stack is the target.
    // Third field is the number of bytes to free/reserve
    // StackControl(StackControlVariant, bool, Bits<5>),

    // load from stack instruction.
    //
    // First is whether the loaded value is signed.
    // Second is the length of the loaded value.
    // Third is the size of the loaded value.
    // Fourth is the stack address offset.
    // LoadStack(bool, Bits<3>, Bits<3>, Bits<6>),
}
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
