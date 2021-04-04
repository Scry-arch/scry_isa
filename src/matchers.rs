use crate::{Bits};
use std::marker::PhantomData;

pub trait Parser
{
	type Internal;
	
	fn parse(tokens: &[&str] ) -> Result<(Self::Internal, usize), usize>;
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result;
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

pub struct Then<P1: Parser, P2: Parser>(PhantomData<P1>, PhantomData<P2>);
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