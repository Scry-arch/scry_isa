use crate::{Instruction, Bits, CallVariant};
use std::marker::PhantomData;
use std::collections::HashMap;
use lazy_static::lazy_static;

pub trait Parser
{
	type Internal;
	
	fn parse(tokens: &[&str] ) -> Result<(Self::Internal, usize), usize>;
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result;
}

pub struct InstructionParser();

impl Parser for InstructionParser
{
	type Internal = Instruction;
	fn parse(tokens: &[&str] ) -> Result<(Self::Internal, usize), usize>
	{
		lazy_static!{
			static ref MNEMONIC_PARSERS: HashMap<&'static str, fn(&[&str]) -> std::result::Result<(Instruction, usize), usize>> = {
				let mut mnem_pars:  HashMap<&'static str, fn(&[&str]) -> std::result::Result<(Instruction, usize), usize>>  = HashMap::new();
				mnem_pars.insert("jmp", {
					fn parse(tokens: &[&str] ) -> Result<(Instruction, usize), usize>
					{
						let ((imm, loc), consumed) = Then::<CommaAfterParser<ReferenceParser<7,true>>,ReferenceParser<6,false>>::parse(tokens)?;
						Ok((Instruction::Jump(imm, loc), consumed))
					}
					parse
				});
				mnem_pars.insert("ret", {
					fn parse(tokens: &[&str] ) -> Result<(Instruction, usize), usize>
					{
						let (loc, consumed) = ReferenceParser::<6,false>::parse(tokens)?;
						Ok((Instruction::Call(CallVariant::Ret, loc), consumed))
					}
					parse
				});
				mnem_pars
			};
		}
		
		let mnemonic = tokens.iter().next().ok_or_else(|| 0usize)?;
		if let Some(parser) = MNEMONIC_PARSERS.get(mnemonic) {
			let tokens = tokens.split_at(1).1;
			parser(tokens).map_or_else(|idx| Err(idx+1), |(instr, consumed)| Ok((instr, consumed+1)))
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
			Jump(imm, loc) => {
				Then::<CommaAfterParser<ReferenceParser<7,true>>,ReferenceParser<6,false>>::print(&(*imm, *loc), out)
			}
			Call(_, loc) => {
				ReferenceParser::<6,false>::print(&(*loc), out)
			}
			_ => todo!()
		}
	}
}

pub struct ReferenceParser<const SIZE: u32, const SIGNED: bool>();

impl<const SIZE: u32, const SIGNED: bool> Parser for ReferenceParser<SIZE, SIGNED>
{
	type Internal = Bits<SIZE>;
	fn parse( tokens: &[&str] ) -> Result<(Self::Internal, usize), usize>
	{
		let value = tokens.iter().next().ok_or_else(|| 0usize)?;
		if SIGNED {
			Bits::new_signed(value.parse().map_err(|_|0usize)?)
		}else {
			Bits::new_unsigned(value.parse().map_err(|_|0usize)?)
		}.map_or_else(||Err(0), |b|{
			Ok((b,1))
		})
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		out.write_str(
			if SIGNED {
				internal.value().to_string()
			} else {
				(internal.value() as u16).to_string()
			}.as_str()
		)
	}
}

pub struct CommaAfterParser<P: Parser>(PhantomData<P>);

impl<P:Parser> Parser for CommaAfterParser<P>
{
	type Internal = P::Internal;
	
	fn parse(tokens: &[&str]) -> Result<(Self::Internal, usize), usize> {
		let t = tokens.iter().next().ok_or_else(|| 0usize)?;
		if t.ends_with(",") {
			let t = t.split_at(t.len()-1).0;
			P::parse(&[t])
		} else {
			let result = P::parse(&[t])?;
			let comma = tokens.iter().nth(1).ok_or_else(|| 1usize)?;
			if comma == &"," {
				Ok((result.0, result.1 + 1))
			} else {
				Err(result.1)
			}
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		P::print(internal, out)?;
		out.write_str(",")
	}
}

struct Then<P1: Parser, P2: Parser>(PhantomData<P1>, PhantomData<P2>);
impl<P1: Parser, P2: Parser> Parser for Then<P1,P2>
{
	type Internal = (P1::Internal, P2::Internal);
	
	fn parse(tokens: &[&str]) -> Result<(Self::Internal, usize), usize> {
		
		let (result1, consumed) = P1::parse(tokens)?;
		let next_tokens = tokens.split_at(1).1;
		
		match P2::parse(next_tokens) {
			Ok((result2, consumed2)) => Ok(((result1, result2), consumed + consumed2)),
			Err(idx) => Err(idx + consumed)
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		P1::print(&internal.0, out)?;
		out.write_str(" ")?;
		P2::print(&internal.1,out)
	}
}