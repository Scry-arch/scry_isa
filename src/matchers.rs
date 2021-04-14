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
	
	/// Tries parsing the given tokens.
	///
	/// If successful, returns the parse result, the number of tokens consumed excluding the last,
	/// and the number of consumed bytes in the last token.
	/// E.g. (_, 3, 2) means 3 tokens were fully consumed and 2 bytes were consumed from the fourth
	/// token.
	/// (_, 0, 2) means on the first 2 bytes from the first token were consumed.
	/// (_, 0, 0) means nothing was consumed.
	/// It is valid to have a successful parsing that consumed nothing.
	///
	/// The given function is used for resolving distances (in bytes) between symbols.
	/// If (Some(x), y) should return the distance between symbols x and y.
	/// If x has a lower address than y, the result should be positive.
	/// If x has a higher adderss than y, the result should be negative.
	/// If (None, y), the first symbol is the one for the current instruction being parsed.
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, _: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize;
	
	fn print_with_whitespace(internal: &Self::Internal, prev_alone: bool, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		if prev_alone && Self::ALONE_LEFT {
			out.write_char(' ')?;
		}
		Self::print(internal, out)
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result;
}

impl Parser for u16 {
	type Internal = u16;
	const ALONE_RIGHT: bool = true;
	const ALONE_LEFT: bool = true;
	
	fn parse<'a, F>(mut tokens: impl Iterator<Item=&'a str> + Clone, _: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		let value_string = tokens.next()
			// Extract digits from beginning
			.map(|t| t.splitn(2, |c| !char::is_digit(c, 10)).next().unwrap())
			.ok_or_else(|| 0usize)?;
		value_string.parse().map(|v| (v, 0, value_string.len())).map_err(|_| 0usize)
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		out.write_str(
			internal.to_string().as_str()
		)
	}
}

impl Parser for i32 {
	type Internal = i32;
	const ALONE_RIGHT: bool = true;
	const ALONE_LEFT: bool = true;
	
	fn parse<'a, F>(mut tokens: impl Iterator<Item=&'a str> + Clone, _: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		
		let value_string = tokens.next()
			// Extract digits from beginning
			.map(|first_token| first_token.splitn(2, |c| (!char::is_digit(c, 10)) && (c != '-')).next().unwrap())
			.ok_or_else(|| 0usize)?;
		value_string.parse().map(|v| (v, 0, value_string.len())).map_err(|_| 0usize)
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		out.write_str(
			internal.to_string().as_str()
		)
	}
}

pub struct Offset<const SIZE: u32, const SIGNED: bool>();
impl<const SIZE: u32, const SIGNED: bool> Parser for Offset<SIZE, SIGNED>
{
	type Internal = Bits<SIZE, SIGNED>;
	const ALONE_RIGHT: bool = true;
	const ALONE_LEFT: bool = true;
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		if SIGNED {
			i32::parse(tokens, f).and_then(|(value, consumed, bytes)|
				Bits::new(value).map_or_else(
					||Err(0),
					|b|Ok((b, consumed,bytes)))
			)
		} else {
			u16::parse(tokens, f).and_then(|(value, consumed, bytes)|
				Bits::new(value as i32).map_or_else(
					||Err(0),
					|b|Ok((b, consumed,bytes)))
			)
		}
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		i32::print(&internal.value(), out)
	}
}

pub struct ReferenceParser<const SIZE: u32>();
impl<const SIZE: u32> Parser for ReferenceParser<SIZE>
{
	type Internal = Bits<SIZE, false>;
	const ALONE_RIGHT: bool = true;
	const ALONE_LEFT: bool = true;
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		Then::<Arrow, u16>::parse(tokens, f).and_then(|(((),value), consumed, bytes)|
			Bits::new(value as i32).map_or_else(
				||Err(0),
				|b|Ok((b, consumed,bytes)))
		)
	}
	
	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		Then::<Arrow, u16>::print(&((), internal.value() as u16), out)
	}
}

pub struct CommaBetween<P1: Parser, P2: Parser>(PhantomData<(P1, P2)>);

impl<P1:Parser, P2: Parser> Parser for CommaBetween<P1, P2>
{
	type Internal = (P1::Internal, P2::Internal);
	const ALONE_RIGHT: bool = P2::ALONE_RIGHT;
	const ALONE_LEFT: bool = P1::ALONE_LEFT;
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		Then::<P1, Then<Comma, P2>>::parse(tokens, f).map(|((left, ((), right)), tokens, bytes)| ((left, right), tokens, bytes))
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
	
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		match P1::parse(tokens.clone(), f) {
			Ok((result1, consumed1, bytes1)) => {
				let mut tokens = tokens.skip(consumed1);
				let first_next_token =  tokens.next().map(|t| t.split_at(bytes1).1)
					.filter(|t| !t.is_empty());
				
				match P2::parse(first_next_token.into_iter().chain(tokens), f) {
					Ok((result2, 0, 0)) => Ok(((result1, result2), consumed1, bytes1)),
					Ok((result2, consumed2, bytes2)) => Ok((
						(result1, result2),
						consumed1 + consumed2 + ((first_next_token.is_none()) as usize),
						bytes2 + (bytes1 * ((first_next_token.is_some() && consumed2 == 0) as usize))
					)),
					Err(idx) => Err(consumed1 + idx)
				}
			}
			Err(idx) => Err(idx)
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
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		let err1 = match P1::parse(tokens.clone(), f) {
			Ok((result, consumed, bytes)) => match result.try_into() {
				Ok(result) => return Ok((result, consumed, bytes)),
				_ => 0
			},
			Err(idx) => idx
		};
		
		match P2::parse(tokens, f) {
			Ok((parsed, consumed, bytes)) => {
				match parsed.try_into() {
					Ok(result) => Ok((result, consumed, bytes)),
					_ => Err(err1)
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
	
	fn parse<'a, F>(mut tokens: impl Iterator<Item=&'a str> + Clone, _: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		tokens.next().filter(|t| t.starts_with(I::IDENT))
			.map(|_| ((), 0, I::IDENT.len()))
			.ok_or(0)
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
		
		fn parse<'a, F>(mut tokens: impl Iterator<Item=&'a str> + Clone, _: &F) -> Result<(Self::Internal, usize, usize), usize>
			where F: Fn(Option<&str>, &str) -> isize
		{
			tokens.next().filter(|t| t.starts_with(text))
				.map(|_| ((), 0, text.len()))
				.ok_or(0)
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
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		match P::parse(tokens, f) {
			Ok((result, consumed, bytes)) => Ok((Some(result), consumed, bytes)),
			Err(_) => Ok((None, 0, 0)),
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
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		match P::parse(tokens, f) {
			Ok((_, consumed, bytes)) => Ok((true, consumed, bytes)),
			Err(_) => Ok((false, 0, 0)),
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
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		match P1::parse(tokens.clone(), f) {
			Ok((_, consumed, bytes)) => Ok((true, consumed, bytes)),
			Err(err1) => match P2::parse(tokens, f) {
				Ok((_, consumed, bytes)) => Ok((false, consumed, bytes)),
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
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		let (result, consumed, bytes) = P::parse(tokens,f)?;
		if let Ok(result) = result.try_into() {
			Ok((result, consumed, bytes))
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
	
	fn parse<'a, F>(tokens: impl Iterator<Item=&'a str> + Clone, f: &F) -> Result<(Self::Internal, usize, usize), usize>
		where F: Fn(Option<&str>, &str) -> isize
	{
		P::parse(tokens,f)
	}
	
	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
		P::print(internal, out)
	}
}
