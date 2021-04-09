use crate::instructions::{
	Bits, Alu2OutputVariant
};
use std::marker::PhantomData;
use std::convert::{TryFrom, TryInto};
use std::fmt::Write;
use std::cmp::max;
use duplicate::duplicate_inline;

pub trait Parser
{
	type Internal;
	
	const ALONE_RIGHT: bool;
	const ALONE_LEFT: bool;
	fn parse_ending(_: &str) -> Option<(&str, &str)>
	{
		None
	}
	fn parse_start(_: &str) -> Option<(&str, &str)>
	{
		None
	}
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str>  + Clone) -> Result<(Self::Internal, usize), usize>;
	
	fn print_with_whitespace(internal: &Self::Internal, prev_alone: bool, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		if prev_alone && Self::ALONE_LEFT {
			out.write_char(' ')?;
		}
		Self::print(internal, out)
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result;
}

pub struct ReferenceParser<const SIZE: u32, const SIGNED: bool>();

impl<const SIZE: u32, const SIGNED: bool> Parser for ReferenceParser<SIZE, SIGNED>
{
	type Internal = Bits<SIZE, SIGNED>;
	const ALONE_RIGHT: bool = true;
	const ALONE_LEFT: bool = true;
	
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
	const ALONE_RIGHT: bool = P2::ALONE_RIGHT;
	const ALONE_LEFT: bool = P1::ALONE_LEFT;
	
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
		Comma::print_with_whitespace(&(),P1::ALONE_RIGHT, out)?;
		P2::print_with_whitespace(&internal.1, Comma::ALONE_RIGHT, out)
	}
}

pub struct Then<P1: Parser, P2: Parser>(PhantomData<(P1,P2)>);
impl<P1: Parser, P2: Parser> Parser for Then<P1,P2>
{
	type Internal = (P1::Internal, P2::Internal);
	const ALONE_RIGHT: bool = P2::ALONE_RIGHT;
	const ALONE_LEFT: bool = P1::ALONE_LEFT;
	
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
		P2::print_with_whitespace(&internal.1, P1::ALONE_RIGHT, out)
	}
}

pub struct Or<P1: Parser, P2: Parser, T>(PhantomData<(P1,P2,T)>)
	where
		T: Copy + TryFrom<P1::Internal> + TryFrom<P2::Internal>,
		P1::Internal: TryFrom<T>,
		P2::Internal: TryFrom<T>,;
impl<P1: Parser, P2: Parser, T> Parser for Or<P1,P2,T>
	where
		T: Copy + TryFrom<P1::Internal> + TryFrom<P2::Internal>,
		P1::Internal: TryFrom<T>,
		P2::Internal: TryFrom<T>,
{
	type Internal = T;
	const ALONE_RIGHT: bool = P1::ALONE_RIGHT || P2::ALONE_RIGHT;
	const ALONE_LEFT: bool = P1::ALONE_LEFT || P2::ALONE_LEFT;
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {
		let err1 = match P1::parse(tokens.clone()) {
			Ok((result, consumed)) => match result.try_into() {
				Ok(result) => return Ok((result, consumed)),
				_ => 0
			},
			Err(idx) => idx
		};
		
		match P2::parse(tokens) {
			Ok((parsed, consumed)) => {
				match parsed.try_into() {
					Ok(result) => Ok((result, consumed)),
					_ => Err(0 + err1)
				}
			},
			Err(err2) => Err(max(err1, err2))
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		if let Ok(internal) = (*internal).try_into() {
			P1::print(&internal, out)
		} else if let Ok(internal) = (*internal).try_into() {
			P2::print(&internal, out)
		}else {
			panic!("Unsupported")
		}
	}
}

pub trait HasIdent
{
	const IDENT: &'static str;
}

pub struct Ident<I: HasIdent>(PhantomData<I>);
impl<I: HasIdent> Parser for Ident<I>
{
	type Internal = ();
	const ALONE_RIGHT: bool = true;
	const ALONE_LEFT: bool = true;
	
	fn parse<'a>(mut tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {
		if let Some(next) = tokens.next() {
			if next == I::IDENT {
				return Ok(((), 1))
			}
		}
		Err(0)
	}
	
	fn print(_: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		out.write_str(I::IDENT)
	}
}

duplicate_inline! {
	[
		name	text;
		[High]	["High"];
		[Low]	["Low"];
	]
	pub struct name();
	impl HasIdent for name
	{
		const IDENT:&'static str = text;
	}
}

duplicate_inline!{
	[
		name	text		alone_right;
		[Arrow]	["->"]		[false];
		[Comma]	[","]		[true];
		[Plus]	["+"]		[false];
	]
	pub struct name();
	impl Parser for name
	{
		type Internal = ();
		const ALONE_RIGHT: bool = alone_right;
		const ALONE_LEFT: bool = false;
		
		fn parse_ending(token: &str) -> Option<(&str, &str)>
		{
			token.find(text).map(|idx| {
				token.split_at(idx)
			})
		}
		fn parse_start(token: &str) -> Option<(&str, &str)>
		{
			token.find(text).map(|idx|
				token.split_at(idx+text.len())
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
			out.write_str(text)
		}
	}
}

pub struct Maybe<P:Parser>(PhantomData<P>);
impl<P:Parser> Parser for Maybe<P>
{
	type Internal = Option<P::Internal>;
	const ALONE_RIGHT: bool = P::ALONE_RIGHT;
	const ALONE_LEFT: bool = P::ALONE_LEFT;
	
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
	const ALONE_RIGHT: bool = P::ALONE_RIGHT;
	const ALONE_LEFT: bool = P::ALONE_LEFT;
	
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

pub struct Flag<P1:Parser, P2:Parser>(PhantomData<(P1,P2)>)
	where P1::Internal: Default, P2::Internal: Default;
impl<P1:Parser, P2:Parser> Parser for Flag<P1, P2>
	where P1::Internal: Default, P2::Internal: Default
{
	type Internal = bool;
	const ALONE_RIGHT: bool = P1::ALONE_RIGHT || P2::ALONE_RIGHT;
	const ALONE_LEFT: bool = P1::ALONE_LEFT || P2::ALONE_LEFT;
	
	fn parse_ending(token: &str) -> Option<(&str, &str)>
	{
		P1::parse_ending(token).or_else(||
			P2::parse_ending(token)
		)
	}
	fn parse_start(token: &str) -> Option<(&str, &str)>
	{
		P1::parse_start(token).or_else(||
			P2::parse_start(token)
		)
	}
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {
		match P1::parse(tokens.clone()) {
			Ok((_, consumed)) => Ok((true, consumed)),
			Err(err1) => match P2::parse(tokens) {
				Ok((_, consumed)) => Ok((false, consumed)),
				Err(err2) => Err(std::cmp::max(err1, err2)),
			},
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		if *internal {
			P1::print(&P1::Internal::default(), out)
		} else {
			P2::print(&P2::Internal::default(), out)
		}
	}
}

impl TryFrom<(bool, Option<(bool, bool)>)> for Alu2OutputVariant
{
	type Error = ();
	
	fn try_from(value: (bool, Option<(bool, bool)>)) -> Result<Self, Self::Error> {
		use Alu2OutputVariant::*;
		Ok(match value {
			(true, Some((true, false))) => NextLow,
			(true, Some((false, false))) => FirstHigh,
			(false, Some((true, true))) => NextHigh,
			(false, Some((false, true))) => FirstLow,
			(true, None) => High,
			(false, None) => Low,
			_ => return Err(())
		})
	}
}
impl From<&Alu2OutputVariant> for (bool, Option<(bool, bool)>)
{
	fn from(v: &Alu2OutputVariant) -> Self {
		use Alu2OutputVariant::*;
		match v {
			High => (true, None),
			Low => (false, None),
			FirstHigh => (true, Some((false, false))),
			FirstLow => (false, Some((false, true))),
			NextHigh => (false, Some((true, true))),
			NextLow => (true, Some((true, false)))
		}
	}
}

pub struct Flatten<P: Parser, T>(PhantomData<(P,T)>)
	where
		T: TryFrom<P::Internal>,
		P::Internal: for<'a> From<&'a T>;
impl<P: Parser, T> Parser for Flatten<P,T>
	where
		T: TryFrom<P::Internal>,
		P::Internal: for<'a> From<&'a T>
{
	type Internal = T;
	const ALONE_RIGHT: bool = P::ALONE_RIGHT;
	const ALONE_LEFT: bool = P::ALONE_LEFT;
	
	fn parse_ending(token: &str) -> Option<(&str, &str)> {
		P::parse_ending(token)
	}
	
	fn parse_start(token: &str) -> Option<(&str, &str)> {
		P::parse_start(token)
	}
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {
		let (result, consumed) = P::parse(tokens)?;
		if let Ok(result) = result.try_into() {
			Ok((result, consumed))
		} else {
			Err(0)
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		P::print(&internal.into(), out)
	}
}

pub struct Alone<P:Parser>(PhantomData<P>);
impl<P: Parser> Parser for Alone<P>
{
	type Internal = P::Internal;
	const ALONE_RIGHT: bool = true;
	const ALONE_LEFT: bool = true;
	
	fn parse_ending(t: &str) -> Option<(&str, &str)> {
		P::parse_ending(t)
	}
	
	fn parse_start(t: &str) -> Option<(&str, &str)> {
		P::parse_start(t)
	}
	
	fn parse<'a>(tokens: impl Iterator<Item=&'a str> + Clone) -> Result<(Self::Internal, usize), usize> {
		P::parse(tokens)
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		P::print(internal, out)
	}
}
