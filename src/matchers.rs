use crate::instructions::Bits;
use std::marker::PhantomData;
use std::convert::{TryFrom, TryInto};
use std::fmt::Write;
use std::cmp::max;
use duplicate::duplicate_inline;

pub trait Parser
{
	type Internal;
	
	fn parse_ending(_: &str) -> Option<(&str, &str)>
	{
		None
	}
	fn parse_start(_: &str) -> Option<(&str, &str)>
	{
		None
	}
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str>  + Clone) -> Result<(Self::Internal, usize), usize>;
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result;
}

pub struct ReferenceParser<const SIZE: u32, const SIGNED: bool>();

impl<const SIZE: u32, const SIGNED: bool> Parser for ReferenceParser<SIZE, SIGNED>
{
	type Internal = Bits<SIZE, SIGNED>;
	
	fn parse<'a>(mut tokens: impl Iterator<Item=&'a str>  + Clone) -> Result<(Self::Internal, usize), usize>
	{
		let value = tokens.next().ok_or_else(|| 0usize)?;
		Bits::new(value.parse().map_err(|_|0usize)?).map_or_else(||Err(0), |b|Ok((b,1)))
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		out.write_str(
			internal.value().to_string().as_str()
		)
	}
}

pub struct CommaBetween<P1: Parser, P2: Parser>(PhantomData<(P1, P2)>);

impl<P1:Parser, P2: Parser> Parser for CommaBetween<P1, P2>
{
	type Internal = (P1::Internal, P2::Internal);
	
	fn parse_ending(token: &str) -> Option<(&str, &str)>
	{
		Then::<P1, Then<Comma, P2>>::parse_ending(token)
	}
	fn parse_start(token: &str) -> Option<(&str, &str)>
	{
		Then::<P1, Then<Comma, P2>>::parse_start(token)
	}
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str>  + Clone) -> Result<(Self::Internal, usize), usize> {
		Then::<P1, Then<Comma, P2>>::parse(tokens).map(|((left, ((), right)), consumed)| ((left, right), consumed))
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		P1::print(&internal.0, out)?;
		Comma::print(&(),out)?;
		P2::print(&internal.1, out)
	}
}

pub struct Then<P1: Parser, P2: Parser>(PhantomData<(P1,P2)>);
impl<P1: Parser, P2: Parser> Parser for Then<P1,P2>
{
	type Internal = (P1::Internal, P2::Internal);
	
	fn parse_ending(token: &str) -> Option<(&str, &str)>
	{
		P1::parse_ending(token)
	}
	fn parse_start(token: &str) -> Option<(&str, &str)>
	{
		P2::parse_start(token)
	}
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {

		let (result1, consumed1, first_next_token) = match P1::parse(tokens.clone()) {
			Ok((result1, consumed1)) => {
				(result1, consumed1, None)
			}
			Err(idx) => {
				// P1 failed to parse, but maybe that is because the last token is shared with p2
				// Therefore, ask P2 to split it
				let idx_token = tokens.clone().nth(idx).ok_or(idx)?;
				if let Some((before, after)) = P2::parse_ending(idx_token) {
					let (result1, consumed1) = P1::parse(tokens.clone().take(idx).chain(Some(before).into_iter()))?;
					(result1, consumed1, Some(after))
				// P2 couldn't split the last token P1 looked at, so see if P1 can parse
				// the start of the first token on its own
				} else if let Some((before, after)) = P1::parse_start(tokens.clone().next().ok_or(idx)?) {
					let (result1, consumed1) = P1::parse(Some(before).into_iter())?;
					(result1, consumed1, Some(after))
				// P1 couldn't parse anything.
				} else {
					return Err(idx);
				}
			}
		};
		let sub_one = first_next_token.is_some();
		match P2::parse(first_next_token.into_iter().chain(tokens.skip(consumed1))) {
			Ok((result2, consumed2)) => Ok(((result1, result2), consumed1 + consumed2 - (sub_one as usize))),
			Err(idx) => Err(idx + consumed1)
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		P1::print(&internal.0, out)?;
		P2::print(&internal.1,out)
	}
}

pub struct Or<P1: Parser, P2: Parser>(PhantomData<(P1,P2)>)
	where P1::Internal: TryFrom<P2::Internal>;
impl<P1: Parser, P2: Parser> Parser for Or<P1,P2>
	where P1::Internal: TryFrom<P2::Internal>
{
	type Internal = P1::Internal;
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {
		match P1::parse(tokens.clone()) {
			Ok(result) => Ok(result),
			Err(idx1) => {
				match P2::parse(tokens) {
					Ok((parsed, consumed)) => {
						match parsed.try_into() {
							Ok(result) => Ok((result, consumed)),
							_ => Err(0)
						}
					},
					Err(idx2) => Err(max(idx1, idx2))
				}
			}
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		P1::print(internal, out)
	}
}

duplicate_inline!{
	[
		name	text	print_as;
		[Arrow]	["->"]	["->"];
		[Comma]	[","]	[", "];
	]
	pub struct name();
	impl Parser for name
	{
		type Internal = ();
	
		fn parse_ending(token: &str) -> Option<(&str, &str)>
		{
			token.find(text).map(|idx| {
				token.split_at(idx)
			})
		}
		fn parse_start(token: &str) -> Option<(&str, &str)>
		{
			token.find(text).map(|idx|
				token.split_at(idx+1)
			)
		}
		
		fn parse<'a>(mut tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {
			if let Some(next) = tokens.next() {
				if next == text {
					return Ok(((), 1))
				}
			}
			Err(0)
		}
		
		fn print(_: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
			out.write_str(print_as)
		}
	}
}

pub struct Maybe<P:Parser>(PhantomData<P>);
impl<P:Parser> Parser for Maybe<P>
{
	type Internal = Option<P::Internal>;
	
	fn parse_ending(token: &str) -> Option<(&str, &str)>
	{
		P::parse_ending(token)
	}
	fn parse_start(token: &str) -> Option<(&str, &str)>
	{
		P::parse_start(token)
	}
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {
		match P::parse(tokens) {
			Ok((result, consumed)) => Ok((Some(result), consumed)),
			Err(_) => Ok((None, 0)),
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		if let Some(internal) = internal {
			P::print(internal, out)
		} else {
			Ok(())
		}
	}
}

pub struct BoolFlag<P:Parser>(PhantomData<P>)
	where P::Internal: Default;
impl<P:Parser> Parser for BoolFlag<P>
	where P::Internal: Default
{
	type Internal = bool;
	
	fn parse_ending(token: &str) -> Option<(&str, &str)>
	{
		P::parse_ending(token)
	}
	fn parse_start(token: &str) -> Option<(&str, &str)>
	{
		P::parse_start(token)
	}
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {
		match P::parse(tokens) {
			Ok((_, consumed)) => Ok((true, consumed)),
			Err(_) => Ok((false, 0)),
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		if *internal {
			P::print(&P::Internal::default(), out)
		} else {
			Ok(())
		}
	}
}