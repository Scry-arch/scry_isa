use crate::{
	instructions::{Alu2OutputVariant, Bits},
	ParseErrorType::OutOfBoundValue,
};
use duplicate::duplicate_inline;
use lazy_static::lazy_static;
use std::{
	borrow::Borrow,
	convert::{TryFrom, TryInto},
	fmt::Write,
	marker::PhantomData,
};

/// The type of error parsing encountered.
#[derive(Debug, Clone)]
pub enum ParseErrorType<'a>
{
	/// Couldn't resolve symbol
	UnkownSymbol,

	/// Invalid inputs.
	///
	/// Given is a description of what was expected of the symbol
	Invalid(&'a str),

	/// Invalid number value.
	///
	/// First element is the found value.
	/// Second is the allowed lower bound
	/// Third is the allowed upper bound.
	OutOfBoundValue(isize, isize, isize),

	/// Unexpected characters.
	///
	/// Given is a description of expected characters.
	UnexpectedChars(&'a str),

	/// Token stream ended unexpectedly.
	EndOfStream,

	/// Internal Error that shouldn't propagate outside the crate.
	///
	/// Please file a bug report with the given string refering to where in the
	/// source the error originates.
	InternalError(&'a str),
}
impl<'a> ParseErrorType<'a>
{
	fn from_bits<const SIZE: u32, const SIGNED: bool>(value: isize) -> Self
	{
		OutOfBoundValue(
			value,
			Bits::<SIZE, SIGNED>::min().value() as isize,
			Bits::<SIZE, SIGNED>::max().value() as isize,
		)
	}
}

/// The span and type of error parsing encountered.
///
/// The span is a range of characters that parsing has deemed the source of the
/// error. It starts in one token, at a specific index, and ranges to another
/// token (or the same) at an index.
#[derive(Debug, Clone)]
pub struct ParseError<'a>
{
	/// The index of the first token in the span
	pub start_token: usize,
	/// The index in the first token at which the span starts.
	pub start_idx: usize,
	/// The index of the last token in the span
	pub end_token: usize,
	/// The index following the last character of the last token in the span
	pub end_idx: usize,
	/// The error type.
	pub err_type: ParseErrorType<'a>,
}
impl<'a> ParseError<'a>
{
	pub fn from_token(token: &str, idx: usize, err_type: ParseErrorType<'a>) -> Self
	{
		Self {
			start_token: idx,
			start_idx: 0,
			end_token: idx,
			end_idx: token.len(),
			err_type,
		}
	}

	pub fn from_no_span(err_type: ParseErrorType<'a>) -> Self
	{
		Self {
			start_token: 0,
			start_idx: 0,
			end_token: 0,
			end_idx: 0,
			err_type,
		}
	}

	pub fn replace_if_further(&mut self, other: &Self)
	{
		let other_start_after = self.start_token < other.start_token
			|| (self.start_token == other.start_token && self.start_idx < other.start_idx);
		let other_start_equal =
			self.start_token == other.start_token && self.start_idx == other.start_idx;

		let self_end_after = self.end_token > other.end_token
			|| (self.end_token == other.end_token && self.end_idx > other.end_idx);

		if other_start_after || (other_start_equal && self_end_after)
		{
			*self = other.clone();
		}
	}
}

pub trait Parser<'a>
{
	type Internal;

	const ALONE_RIGHT: bool;
	const ALONE_LEFT: bool;

	/// Tries parsing the given tokens.
	///
	/// If successful, returns the parse result, the number of tokens consumed
	/// excluding the last, and the number of consumed bytes in the last token.
	/// E.g. (_, 3, 2) means 3 tokens were fully consumed and 2 bytes were
	/// consumed from the fourth token.
	/// (_, 0, 2) means on the first 2 bytes from the first token were consumed.
	/// (_, 0, 0) means nothing was consumed.
	/// It is valid to have a successful parsing that consumed nothing.
	///
	/// The given function is used for resolving distances (in bytes) between
	/// symbols. If (Some(x), y) should return the distance between symbols x
	/// and y. If x has a lower address than y, the result should be positive.
	/// If x has a higher adderss than y, the result should be negative.
	/// If (None, y), the first symbol is the one for the current instruction
	/// being parsed.
	///
	/// The given iterator must produce tokens of only ASCII characters free of
	/// whitespace. Effectively, the iterator must behave as if it was produced
	/// by [`split_ascii_whitespace`](https://doc.rust-lang.org/std/primitive.str.html#method.split_ascii_whitespace)
	fn parse<I, F, B>(tokens: I, _: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32;

	fn print_with_whitespace(
		internal: &Self::Internal,
		prev_alone: bool,
		out: &mut impl std::fmt::Write,
	) -> std::fmt::Result
	{
		if prev_alone && Self::ALONE_LEFT
		{
			out.write_char(' ')?;
		}
		Self::print(internal, out)
	}

	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result;
}

/// Advances the given iterator according to the given consumed and bytes
/// values. Returns new consumed and bytes values, where if the bytes have
/// consumed their token, it is reflected in the consumed (which is then 1
/// higher) and the bytes are set to 0. Lastly, returns the iterator advanced to
/// the token/bytes after the consumed.
///
/// Returns: (consumed, bytes, tokens)
fn advance_iterator<'a>(
	tokens: impl Iterator<Item = &'a str> + Clone,
	consumed: usize,
	bytes: usize,
) -> (usize, usize, impl Iterator<Item = &'a str> + Clone)
{
	let mut tokens = tokens.skip(consumed);
	let mut consumed_last = false;
	let first_next = tokens.next().map(|t| t.split_at(bytes).1).filter(|t| {
		consumed_last = t.is_empty();
		!consumed_last
	});
	(
		consumed + consumed_last as usize, // increment if bytes consumed last token
		bytes * (!consumed_last as usize), // Set to zero if bytes consumed last token.
		first_next.into_iter().chain(tokens),
	)
}

impl<'a> Parser<'a> for ()
{
	type Internal = ();

	const ALONE_LEFT: bool = false;
	const ALONE_RIGHT: bool = false;

	fn parse<I, F, B>(_: I, _: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		Ok(((), 0, 0))
	}

	fn print_with_whitespace(_: &Self::Internal, _: bool, _: &mut impl Write) -> std::fmt::Result
	{
		Ok(())
	}

	fn print(_: &Self::Internal, _: &mut impl Write) -> std::fmt::Result
	{
		Ok(())
	}
}

impl<'a> Parser<'a> for u16
{
	type Internal = u16;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		let value_string = tokens.next()
			.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
			// Extract digits from beginning
			.map(|t| t.splitn(2, |c| !char::is_digit(c, 10)).next().unwrap())?;
		value_string
			.parse()
			.map(|v| (v, 0, value_string.len()))
			.map_err(|_| {
				ParseError::from_token(
					value_string,
					0,
					ParseErrorType::UnexpectedChars("unsigned integer"),
				)
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		out.write_str(internal.to_string().as_str())
	}
}

impl<'a> Parser<'a> for i32
{
	type Internal = i32;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		let value_string = tokens.next()
			.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
			// Extract digits from beginning
			.map(|first_token| first_token.splitn(2,
				|c| (!char::is_digit(c, 10)) && (c != '-')).next().unwrap()
			)?;
		value_string
			.parse()
			.map(|v| (v, 0, value_string.len()))
			.map_err(|_| {
				ParseError::from_token(
					value_string,
					0,
					ParseErrorType::UnexpectedChars("signed or unsigned integer"),
				)
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		out.write_str(internal.to_string().as_str())
	}
}

impl<'a, const SIZE: u32, const SIGNED: bool> Parser<'a> for Bits<SIZE, SIGNED>
{
	type Internal = Self;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		i32::parse(tokens, f).and_then(|(value, consumed, bytes)| {
			Self::new(value).map_or(
				Err(ParseError {
					start_token: 0,
					start_idx: 0,
					end_token: consumed,
					end_idx: bytes,
					err_type: ParseErrorType::from_bits::<SIZE, SIGNED>(value as isize),
				}),
				|b| Ok((b, consumed, bytes)),
			)
		})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		i32::print(&internal.value, out)
	}
}

pub struct Symbol();
impl<'a> Parser<'a> for Symbol
{
	type Internal = &'a str;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		let error_type =
			ParseErrorType::UnexpectedChars("a symbol that start with a letter, '-', '_', or '.'");
		tokens
			.next()
			.ok_or_else(|| ParseError::from_token("", 0, ParseErrorType::EndOfStream))
			.and_then(|t| {
				if t.starts_with(char::is_numeric)
				{
					Err(ParseError::from_token(t, 0, error_type.clone()))
				}
				else
				{
					Ok(t)
				}
			})
			.and_then(|t| {
				let sym = t
					.splitn(2, |c: char| {
						!(c.is_ascii_alphanumeric() || c == '_' || c == '.')
					})
					.next()
					.unwrap();
				if sym.is_empty()
				{
					Err(ParseError::from_token(t, 0, error_type))
				}
				else
				{
					Ok(sym)
				}
			})
			.map(|sym| (sym, 0, sym.len()))
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		out.write_str(internal)
	}
}

pub struct Offset<const SIZE: u32, const SIGNED: bool>();
impl<'a, const SIZE: u32, const SIGNED: bool> Parser<'a> for Offset<SIZE, SIGNED>
{
	type Internal = Bits<SIZE, SIGNED>;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		let f = f.borrow();
		i32::parse::<_, F, _>(tokens.clone(), f)
			.or_else(|_| {
				Symbol::parse::<_, F, _>(tokens, f).map(|(symbol, consumed, bytes)| {
					let difference = f(None, symbol) / 2;
					(difference - ((difference > 0) as i32), consumed, bytes)
				})
			})
			.and_then(|(value, consumed, bytes)| {
				Bits::<SIZE, SIGNED>::new(value).map_or_else(
					|| {
						Err(ParseError {
							start_token: 0,
							start_idx: 0,
							end_token: consumed,
							end_idx: bytes,
							err_type: ParseErrorType::from_bits::<SIZE, SIGNED>(value as isize),
						})
					},
					|b| Ok((b, consumed, bytes)),
				)
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		i32::print(&internal.value(), out)
	}
}

pub struct ReferenceParser<const SIZE: u32>();
impl<'a, const SIZE: u32> Parser<'a> for ReferenceParser<SIZE>
{
	type Internal = Bits<SIZE, false>;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		let f = f.borrow();
		Then::<Arrow, u16>::parse::<_, F, _>(tokens.clone(), f)
			.and_then(|(((), value), consumed, bytes)| {
				Bits::new(value as i32).map_or_else(
					|| {
						Err(ParseError::from_token(
							tokens.clone().next().unwrap().split_at(2).1,
							consumed,
							ParseErrorType::from_bits::<SIZE, false>(value as isize),
						))
					},
					|b| Ok((b, consumed, bytes)),
				)
			})
			.or_else(|mut err| {
				let mut result = Then::<Arrow, Symbol>::parse::<_, F, _>(tokens.clone(), f)
					.and_then(|(((), sym1), consumed, bytes)| {
						let off1 = (f.borrow()(None, sym1) / 2) - 1;
						if off1 < 0
						{
							Err(ParseError {
								start_token: consumed,
								start_idx: 2 * ((consumed == 0) as usize),
								end_token: consumed,
								end_idx: (2 * ((consumed == 0) as usize)) + sym1.len(),
								err_type: ParseErrorType::Invalid(
									"must be at or follow the instruction",
								),
							})
						}
						else
						{
							Ok(((sym1, off1), consumed, bytes))
						}
					});
				let mut next_branch_to = true;
				let mut next_result = result.clone();
				while let Ok(((sym1, offset), consumed, bytes)) = next_result
				{
					result = Ok(((sym1, offset), consumed, bytes));
					let (consumed, bytes, tokens) =
						advance_iterator(tokens.clone(), consumed, bytes);

					next_result = Then::<Arrow, Symbol>::parse::<_, F, _>(tokens, f).and_then(
						|(((), sym), consumed2, bytes2)| {
							let next_consumed = consumed + consumed2;
							let next_bytes = bytes2 + (bytes * ((consumed2 == 0) as usize));

							if next_branch_to
							{
								Ok(((sym, offset), next_consumed, next_bytes))
							}
							else
							{
								let next_offset = f.borrow()(Some(sym1), sym) / 2;
								if next_offset < 0
								{
									Err(ParseError {
										start_token: next_consumed,
										start_idx: bytes * ((consumed2 == 0) as usize),
										end_token: next_consumed,
										end_idx: sym.len() + (bytes * ((consumed2 == 0) as usize)),
										err_type: ParseErrorType::Invalid(
											"must refer to an address higher than the previous \
											 label in the chain",
										),
									})
								}
								else
								{
									Ok(((sym, offset + next_offset), next_consumed, next_bytes))
								}
							}
						},
					);
					next_branch_to = !next_branch_to;
				}
				result.and_then(|((_, offset), consumed, bytes)| {
					Bits::new(offset)
						.ok_or({
							err.replace_if_further(&ParseError {
								start_token: 0,
								start_idx: 0,
								end_token: consumed,
								end_idx: bytes,
								err_type: ParseErrorType::from_bits::<SIZE, false>(offset as isize),
							});
							err
						})
						.map(|b| (b, consumed, bytes))
				})
			})
			.or_else(|err| {
				Arrow::parse::<_, F, _>(tokens.clone(), f)
					.and_then(|(_, consumed, bytes)| {
						Bits::new(0)
							.ok_or(ParseError {
								start_token: 0,
								start_idx: 0,
								end_token: consumed,
								end_idx: bytes,
								err_type: ParseErrorType::InternalError(concat!(
									file!(),
									':',
									line!()
								)),
							})
							.map(|b| (b, consumed, bytes))
					})
					.map_err(|_| err)
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		Then::<Arrow, u16>::print(&((), internal.value() as u16), out)
	}
}

pub struct CommaBetween<'a, P1: 'a + Parser<'a>, P2: 'a + Parser<'a>>(PhantomData<&'a (P1, P2)>);

impl<'a, P1: 'a + Parser<'a>, P2: 'a + Parser<'a>> Parser<'a> for CommaBetween<'a, P1, P2>
{
	type Internal = (P1::Internal, P2::Internal);

	const ALONE_LEFT: bool = P1::ALONE_LEFT;
	const ALONE_RIGHT: bool = P2::ALONE_RIGHT;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		Then::<P1, Then<Comma, P2>>::parse(tokens, f)
			.map(|((left, ((), right)), tokens, bytes)| ((left, right), tokens, bytes))
	}

	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		P1::print(&internal.0, out)?;
		Comma::print_with_whitespace(&(), P1::ALONE_RIGHT, out)?;
		P2::print_with_whitespace(&internal.1, Comma::ALONE_RIGHT, out)
	}
}

pub struct Then<'a, P1: 'a + Parser<'a>, P2: 'a + Parser<'a>>(PhantomData<&'a (P1, P2)>);
impl<'a, P1: 'a + Parser<'a>, P2: 'a + Parser<'a>> Parser<'a> for Then<'a, P1, P2>
{
	type Internal = (P1::Internal, P2::Internal);

	const ALONE_LEFT: bool = P1::ALONE_LEFT;
	const ALONE_RIGHT: bool = P2::ALONE_RIGHT;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		let f = f.borrow();
		match P1::parse::<_, F, _>(tokens.clone(), f)
		{
			Ok((result1, consumed1, bytes1)) =>
			{
				let (consumed, bytes, tokens) = advance_iterator(tokens, consumed1, bytes1);

				match P2::parse::<_, F, _>(tokens, f)
				{
					// If P2 didn't consume anything, report the raw consumed/bytes of P1
					Ok((result2, 0, 0)) => Ok(((result1, result2), consumed1, bytes1)),
					Ok((result2, consumed2, bytes2)) =>
					{
						Ok((
							(result1, result2),
							consumed + consumed2,
							bytes2 + (bytes * ((consumed2 == 0) as usize)),
						))
					},
					Err(err) =>
					{
						Err(ParseError {
							start_token: consumed + err.start_token,
							start_idx: err.start_idx + ((err.start_token == 0) as usize * bytes),
							end_token: consumed + err.end_token,
							end_idx: err.end_idx + ((err.end_token == 0) as usize * bytes),
							err_type: err.err_type,
						})
					},
				}
			},
			Err(err) => Err(err),
		}
	}

	fn print_with_whitespace(
		internal: &Self::Internal,
		prev_alone: bool,
		out: &mut impl Write,
	) -> std::fmt::Result
	{
		P1::print_with_whitespace(&internal.0, prev_alone, out)?;
		P2::print_with_whitespace(&internal.1, P1::ALONE_RIGHT, out)
	}

	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		P1::print(&internal.0, out)?;
		P2::print_with_whitespace(&internal.1, P1::ALONE_RIGHT, out)
	}
}

pub struct Or<'a, P1: 'a + Parser<'a>, P2: 'a + Parser<'a>, T>(PhantomData<&'a (P1, P2, T)>)
where
	T: Copy + TryFrom<P1::Internal> + TryFrom<P2::Internal>,
	P1::Internal: TryFrom<T>,
	P2::Internal: TryFrom<T>;
impl<'a, P1: 'a + Parser<'a>, P2: 'a + Parser<'a>, T> Parser<'a> for Or<'a, P1, P2, T>
where
	T: Copy + TryFrom<P1::Internal> + TryFrom<P2::Internal>,
	P1::Internal: TryFrom<T>,
	P2::Internal: TryFrom<T>,
{
	type Internal = T;

	const ALONE_LEFT: bool = P1::ALONE_LEFT || P2::ALONE_LEFT;
	const ALONE_RIGHT: bool = P1::ALONE_RIGHT || P2::ALONE_RIGHT;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		let f = f.borrow();
		let err1 = match P1::parse::<_, F, _>(tokens.clone(), f)
		{
			Ok((result, consumed, bytes)) =>
			{
				match result.try_into()
				{
					Ok(result) => return Ok((result, consumed, bytes)),
					_ =>
					{
						ParseError {
							start_token: 0,
							start_idx: 0,
							end_token: consumed,
							end_idx: bytes,
							err_type: ParseErrorType::InternalError(concat!(file!(), ':', line!())),
						}
					},
				}
			},
			Err(err) => err,
		};

		match P2::parse::<_, F, _>(tokens, f)
		{
			Ok((parsed, consumed, bytes)) =>
			{
				match parsed.try_into()
				{
					Ok(result) => Ok((result, consumed, bytes)),
					_ => Err(err1),
				}
			},
			Err(mut err2) =>
			{
				Err({
					err2.replace_if_further(&err1);
					err2
				})
			},
		}
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		if let Ok(internal) = (*internal).try_into()
		{
			P1::print(&internal, out)
		}
		else if let Ok(internal) = (*internal).try_into()
		{
			P2::print(&internal, out)
		}
		else
		{
			panic!("Unsupported")
		}
	}
}

pub trait HasWord
{
	const WORD: &'static str;
}

pub struct Keyword<T: HasWord>(PhantomData<T>);
impl<'a, T: HasWord> Parser<'a> for Keyword<T>
{
	type Internal = ();

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		tokens
			.next()
			.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
			.and_then(|t| {
				if t.starts_with(T::WORD)
				{
					Ok(((), 0, T::WORD.len()))
				}
				else
				{
					Err(ParseError::from_token(
						t,
						0,
						ParseErrorType::UnexpectedChars(T::WORD),
					))
				}
			})
	}

	fn print(_: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		out.write_str(T::WORD)
	}
}

duplicate_inline! {
	[
		name	text;
		[High]	["High"];
		[Low]	["Low"];
	]
	pub struct name();
	impl HasWord for name
	{
		const WORD:&'static str = text;
	}
}

duplicate_inline! {
	[
		name	text		alone_right;
		[Arrow]	["=>"]		[false];
		[Comma]	[","]		[true];
		[Plus]	["+"]		[false];
	]
	pub struct name();
	impl<'a> Parser<'a> for name
	{
		type Internal = ();
		const ALONE_RIGHT: bool = alone_right;
		const ALONE_LEFT: bool = false;

		fn parse<I,F,B>(
			mut tokens: I,
			_: B,
		) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
		where
			I: Iterator<Item = &'a str> + Clone,
			B: Borrow<F>,
			F: Fn(Option<&str>, &str) -> i32
		{
			tokens.next()
				.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
				.and_then(|t| if t.starts_with(text) {
					Ok(((), 0, text.len()))
				} else {
					Err(ParseError::from_token(
						t,
						0,
						ParseErrorType::UnexpectedChars(text),
					))
				})
		}

		fn print(_: &Self::Internal, out: &mut impl Write) -> std::fmt::Result {
			out.write_str(text)
		}
	}
}

pub struct Maybe<'a, P: 'a + Parser<'a>>(PhantomData<&'a P>);
impl<'a, P: 'a + Parser<'a>> Parser<'a> for Maybe<'a, P>
{
	type Internal = Option<P::Internal>;

	const ALONE_LEFT: bool = P::ALONE_LEFT;
	const ALONE_RIGHT: bool = P::ALONE_RIGHT;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		match P::parse(tokens, f)
		{
			Ok((result, consumed, bytes)) => Ok((Some(result), consumed, bytes)),
			Err(_) => Ok((None, 0, 0)),
		}
	}

	fn print_with_whitespace(
		internal: &Self::Internal,
		prev_alone: bool,
		out: &mut impl std::fmt::Write,
	) -> std::fmt::Result
	{
		if let Some(_) = internal
		{
			if prev_alone && Self::ALONE_LEFT
			{
				out.write_char(' ')?;
			}
		}
		Self::print(internal, out)
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		if let Some(internal) = internal
		{
			P::print(internal, out)
		}
		else
		{
			Ok(())
		}
	}
}

pub struct BoolFlag<'a, P: 'a + Parser<'a>>(PhantomData<&'a P>)
where
	P::Internal: Default;
impl<'a, P: 'a + Parser<'a>> Parser<'a> for BoolFlag<'a, P>
where
	P::Internal: Default,
{
	type Internal = bool;

	const ALONE_LEFT: bool = P::ALONE_LEFT;
	const ALONE_RIGHT: bool = P::ALONE_RIGHT;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		match P::parse(tokens, f)
		{
			Ok((_, consumed, bytes)) => Ok((true, consumed, bytes)),
			Err(_) => Ok((false, 0, 0)),
		}
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		if *internal
		{
			P::print(&P::Internal::default(), out)
		}
		else
		{
			Ok(())
		}
	}
}

pub struct Flag<'a, P1: 'a + Parser<'a>, P2: 'a + Parser<'a>>(PhantomData<&'a (P1, P2)>)
where
	P1::Internal: Default,
	P2::Internal: Default;
impl<'a, P1: 'a + Parser<'a>, P2: 'a + Parser<'a>> Parser<'a> for Flag<'a, P1, P2>
where
	P1::Internal: Default,
	P2::Internal: Default,
{
	type Internal = bool;

	const ALONE_LEFT: bool = P1::ALONE_LEFT || P2::ALONE_LEFT;
	const ALONE_RIGHT: bool = P1::ALONE_RIGHT || P2::ALONE_RIGHT;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		match P1::parse::<_, F, _>(tokens.clone(), f.borrow())
		{
			Ok((_, consumed, bytes)) => Ok((true, consumed, bytes)),
			Err(err1) =>
			{
				match P2::parse::<_, F, _>(tokens, f)
				{
					Ok((_, consumed, bytes)) => Ok((false, consumed, bytes)),
					Err(mut err2) =>
					{
						Err({
							err2.replace_if_further(&err1);
							err2
						})
					},
				}
			},
		}
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		if *internal
		{
			P1::print(&P1::Internal::default(), out)
		}
		else
		{
			P2::print(&P2::Internal::default(), out)
		}
	}
}

impl TryFrom<(bool, Option<(bool, bool)>)> for Alu2OutputVariant
{
	type Error = ();

	fn try_from(value: (bool, Option<(bool, bool)>)) -> Result<Self, Self::Error>
	{
		use Alu2OutputVariant::*;
		Ok(match value
		{
			(true, Some((true, false))) => NextLow,
			(true, Some((false, false))) => FirstHigh,
			(false, Some((true, true))) => NextHigh,
			(false, Some((false, true))) => FirstLow,
			(true, None) => High,
			(false, None) => Low,
			_ => return Err(()),
		})
	}
}
impl From<&Alu2OutputVariant> for (bool, Option<(bool, bool)>)
{
	fn from(v: &Alu2OutputVariant) -> Self
	{
		use Alu2OutputVariant::*;
		match v
		{
			High => (true, None),
			Low => (false, None),
			FirstHigh => (true, Some((false, false))),
			FirstLow => (false, Some((false, true))),
			NextHigh => (false, Some((true, true))),
			NextLow => (true, Some((true, false))),
		}
	}
}
impl<const SIZE: u32, const SIGNED: bool> TryFrom<(Bits<SIZE, SIGNED>, ())> for Bits<SIZE, SIGNED>
{
	type Error = ();

	fn try_from(value: (Bits<SIZE, SIGNED>, ())) -> Result<Self, Self::Error>
	{
		Ok(value.0)
	}
}
impl<const SIZE: u32, const SIGNED: bool> From<&Bits<SIZE, SIGNED>> for (Bits<SIZE, SIGNED>, ())
{
	fn from(b: &Bits<SIZE, SIGNED>) -> Self
	{
		(b.clone(), ())
	}
}

pub struct Flatten<'a, P: 'a + Parser<'a>, T>(PhantomData<&'a (P, T)>)
where
	T: TryFrom<P::Internal>,
	P::Internal: for<'b> From<&'b T>;
impl<'a, P: 'a + Parser<'a>, T> Parser<'a> for Flatten<'a, P, T>
where
	T: TryFrom<P::Internal>,
	P::Internal: for<'b> From<&'b T>,
{
	type Internal = T;

	const ALONE_LEFT: bool = P::ALONE_LEFT;
	const ALONE_RIGHT: bool = P::ALONE_RIGHT;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		let (result, consumed, bytes) = P::parse(tokens, f)?;
		if let Ok(result) = result.try_into()
		{
			Ok((result, consumed, bytes))
		}
		else
		{
			Err(ParseError {
				start_token: 0,
				start_idx: 0,
				end_token: consumed,
				end_idx: bytes,
				err_type: ParseErrorType::InternalError(concat!(file!(), ':', line!())),
			})
		}
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		P::print(&internal.into(), out)
	}
}

pub struct Alone<'a, P: 'a + Parser<'a>>(PhantomData<&'a P>);
impl<'a, P: 'a + Parser<'a>> Parser<'a> for Alone<'a, P>
{
	type Internal = P::Internal;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		P::parse(tokens, f)
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		P::print(internal, out)
	}
}

pub struct JumpOffsets<'a>(PhantomData<&'a ()>);
impl<'a> Parser<'a> for JumpOffsets<'a>
{
	type Internal = (Bits<7, true>, Bits<6, false>);

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		let starts_with_symbol =
			Symbol::parse(tokens.clone(), |_: Option<&str>, _: &str| 0).is_ok();
		let ((off1, off2), consumed, bytes) =
			CommaBetween::<Offset<8, true>, Offset<6, false>>::parse(tokens, f)?;
		let value = if starts_with_symbol && off1.value() > 0
		{
			// Offset 1 is relative to off2
			off1.value() - off2.value()
		}
		else
		{
			// Ensure right size for offset
			off1.value()
		};
		Bits::new(value).map_or(
			Err(ParseError {
				start_token: 0,
				start_idx: 0,
				end_token: consumed,
				end_idx: bytes,
				err_type: ParseErrorType::from_bits::<7, true>(value as isize),
			}),
			|v| Ok(((v, off2), consumed, bytes)),
		)
	}

	fn print(&(off1, off2): &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		CommaBetween::<Offset<7, true>, Offset<6, false>>::print(&(off1, off2), out)
	}
}

pub struct Pow2<'a, const SIZE: u32>(PhantomData<&'a ()>);
impl<'a, const SIZE: u32> Parser<'a> for Pow2<'a, SIZE>
{
	type Internal = Bits<SIZE, false>;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		tokens
			.next()
			.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
			.and_then(|token| {
				let value_str = token
					.split_at(
						token
							.find(|c: char| !c.is_ascii_digit())
							.unwrap_or(token.len()),
					)
					.0;
				let value_error = Err(ParseError {
					start_token: 0,
					start_idx: 0,
					end_token: 0,
					end_idx: value_str.len(),
					err_type: ParseErrorType::UnexpectedChars("a power of 2"),
				});
				value_str
					.parse::<u16>()
					.map_or(value_error.clone(), |value| {
						if value.count_ones() == 1
						{
							let mut pow = 0;
							let mut v = value >> 1;
							while v != 0
							{
								v >>= 1;
								pow += 1;
							}
							Bits::new(pow)
								.ok_or(ParseError::from_token(
									value_str,
									0,
									ParseErrorType::from_bits::<SIZE, false>(pow as isize),
								))
								.map(|b| (b, 0, value_str.len()))
						}
						else
						{
							value_error
						}
					})
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		let value = 1 << internal.value;
		out.write_fmt(format_args!("{}", value))
	}
}

pub struct IntSize<'a>(PhantomData<&'a ()>);
impl<'a> Parser<'a> for IntSize<'a>
{
	type Internal = (bool, Bits<3, false>);

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		tokens
			.next()
			.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
			.and_then(|token| {
				if token.starts_with('i')
				{
					Ok(true)
				}
				else if token.starts_with('u')
				{
					Ok(false)
				}
				else
				{
					Err(ParseError::from_token(
						token,
						0,
						ParseErrorType::UnexpectedChars("integer scalar size"),
					))
				}
				.and_then(|signed| {
					Pow2::<3>::parse(Some(&token[1..]).into_iter(), f)
						.map_err(|mut err| {
							err.start_idx += 1;
							err
						})
						.map(|(b, _, bytes)| ((signed, b), 0, bytes + 1))
				})
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		out.write_char(if internal.0 { 'i' } else { 'u' })?;
		Pow2::print(&internal.1, out)
	}
}

pub struct VecLength<'a>(PhantomData<&'a ()>);
impl<'a> Parser<'a> for VecLength<'a>
{
	type Internal = Bits<3, false>;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, f: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		Pow2::<3>::parse(tokens.clone(), f)
			.and_then(|(value, consumed, bytes)| {
				if value.is_max()
				{
					Err(ParseError {
						start_token: 0,
						start_idx: 0,
						end_token: consumed,
						end_idx: bytes,
						err_type: ParseErrorType::OutOfBoundValue(value.value as isize, 0, 6),
					})
				}
				else
				{
					Ok((value, consumed, bytes))
				}
			})
			.or_else(|_| {
				tokens
					.next()
					.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
					.and_then(|t| {
						if t.starts_with('_')
						{
							Ok((Bits::max(), 0, 1))
						}
						else
						{
							Err(ParseError::from_token(
								t,
								0,
								ParseErrorType::UnexpectedChars(
									"vector length as '_' or a power of 2",
								),
							))
						}
					})
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		if internal.is_max()
		{
			out.write_char('_')
		}
		else
		{
			Pow2::print(internal, out)
		}
	}
}

pub struct ValueAlias<'a>(PhantomData<&'a ()>);
impl<'a> ValueAlias<'a>
{
	fn value_alias(v: &Bits<8, false>) -> Option<&str>
	{
		lazy_static! {
			static ref ALIASES: Vec<&'static str> = vec!["MAX_VEC_SIZE", "MAX_VEC_ALIGN_MASK",];
		}
		ALIASES.get(v.value as usize).map(|s| *s)
	}
}
impl<'a> Parser<'a> for ValueAlias<'a>
{
	type Internal = Bits<8, false>;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, usize, usize), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Option<&str>, &str) -> i32,
	{
		tokens
			.next()
			.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
			.and_then(|t| {
				duplicate_inline! {
					[
						text 					value;
						["MAX_VEC_SIZE"] 		[0];
						["MAX_VEC_ALIGN_MASK"] 	[1];
					]
					if t.starts_with(text) {
						return Ok((Bits::new(value).unwrap(), 0, text.len()))
					}
				}
				Err(ParseError::from_token(
					t,
					0,
					ParseErrorType::UnexpectedChars("a value alias or integer"),
				))
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		if let Some(alias) = Self::value_alias(internal)
		{
			out.write_str(alias)
		}
		else
		{
			Bits::print(internal, out)
		}
	}
}
