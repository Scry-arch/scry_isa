use crate::{Bits};
use std::marker::PhantomData;

pub trait Parser
{
	type Internal;
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str>  + Clone) -> Result<(Self::Internal, usize), usize>;
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result;
}

pub struct ReferenceParser<const SIZE: u32, const SIGNED: bool>();

impl<const SIZE: u32, const SIGNED: bool> Parser for ReferenceParser<SIZE, SIGNED>
{
	type Internal = Bits<SIZE>;
	fn parse<'a>(mut tokens: impl Iterator<Item=&'a str>  + Clone) -> Result<(Self::Internal, usize), usize>
	{
		let value = tokens.next().ok_or_else(|| 0usize)?;
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

pub struct CommaBetween<P1: Parser, P2: Parser>(PhantomData<(P1, P2)>);

impl<P1:Parser, P2: Parser> Parser for CommaBetween<P1, P2>
{
	type Internal = (P1::Internal, P2::Internal);
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str>  + Clone) -> Result<(Self::Internal, usize), usize> {
		
		let mut last_before = None;
		let mut first_after = None;
		let mut found_comma = false;
		let mut count = 0;
		let before_comma = tokens.clone().take_while(|t| {
			count+=1;
			if t.contains(",") {
				let mut split = t.splitn(2, ",");
				let first = split.next().filter(|string| string != &"");
				let second = split.next().filter(|string| string != &"");
				
				if t.starts_with(",") {
					first_after = first.or(second);
				} else {
					last_before = first;
					first_after = second;
				}
				found_comma = true;
				false
			} else {
				true
			}
		}).collect::<Vec<_>>();
		
		if found_comma {
			let (result1, consumed) = P1::parse(before_comma.into_iter().chain(last_before.into_iter()))?;
			let (result2, consumed2) = P2::parse(first_after.into_iter().chain(tokens.skip(count)))?;
			Ok(((result1, result2), consumed+consumed2))
		} else {
			Err(count)
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		P1::print(&internal.0, out)?;
		out.write_str(", ")?;
		P2::print(&internal.1, out)
	}
}

pub struct Then<P1: Parser, P2: Parser>(PhantomData<P1>, PhantomData<P2>);
impl<P1: Parser, P2: Parser> Parser for Then<P1,P2>
{
	type Internal = (P1::Internal, P2::Internal);
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str>  + Clone) -> Result<(Self::Internal, usize), usize> {
		
		let (result1, consumed) = P1::parse(tokens.clone())?;
		let next_tokens = tokens.skip(consumed);
		
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