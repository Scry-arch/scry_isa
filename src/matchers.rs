use crate::{Alu2OutputVariant, BitValue, Bits, BitsDyn, Exclude};
use duplicate::{duplicate, duplicate_item};
use std::{
	borrow::Borrow,
	convert::{TryFrom, TryInto},
	fmt::{Debug, Write},
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
		ParseErrorType::OutOfBoundValue(
			value,
			Bits::<SIZE, SIGNED>::get_min().value() as isize,
			Bits::<SIZE, SIGNED>::get_max().value() as isize,
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

	pub fn from_consumed(consumed: CanConsume, err_type: ParseErrorType<'a>) -> Self
	{
		Self {
			start_token: 0,
			start_idx: 0,
			end_token: consumed.tokens,
			end_idx: consumed.chars,
			err_type,
		}
	}
}

/// Represents how many tokens and characters a parsing consumed.
///
/// If less than 1 token was consumed, `tokens` will be 0, wile `chars` will
/// contain the number if characters consumed from the first token.
///
/// If only the first token was completely consumed, and no more characters were
/// consumed from the following token, `tokens` will be 0, while `chars` will be
/// the length of the first token.
///
/// If x tokens were fully consumed and y characters were consumed from the
/// following token, `tokens` would be x and `chars` would be y.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CanConsume
{
	/// The number of complete tokens that can be consumed
	pub tokens: usize,

	// The number of bytes that can be consumed from the last token
	pub chars: usize,
}

impl CanConsume
{
	pub fn none() -> Self
	{
		Self {
			tokens: 0,
			chars: 0,
		}
	}

	pub fn chars(chars: usize) -> Self
	{
		Self { tokens: 0, chars }
	}

	/// Advances the given iterator according to this CanConsume.
	/// Returns the consumed tokens/character counts and if the last token was
	/// partially consumed, returns the remaining characters of that token
	/// (since the whole token was consumed from the iterator but some of the
	/// characters weren't). If the iterator is to be used for further parsin,
	/// the returned characters should be prepended to the iterator first (as
	/// their own token).
	pub fn advance_iter_in_place<'a>(
		mut self,
		iter: &mut impl Iterator<Item = &'a str>,
	) -> (Consumed, Option<&'a str>)
	{
		let token = match (self.tokens, self.chars)
		{
			(0, 0) => None,
			(0, c) =>
			{
				let first = iter.next().unwrap();
				assert!(c <= first.len());
				if first.len() == c
				{
					self.tokens += 1;
					self.chars = 0;
					None
				}
				else
				{
					Some(&first[c..])
				}
			},
			(t, c) =>
			{
				let last = iter.nth(t);
				if c == 0
				{
					last
				}
				else
				{
					let last = last.unwrap();
					assert!(last.len() > 0);
					if last.len() == c
					{
						self.tokens += 1;
						self.chars = 0;
						None
					}
					else
					{
						Some(&last[c..])
					}
				}
			},
		};
		(
			Consumed {
				tokens: self.tokens,
				chars: self.chars,
			},
			token,
		)
	}

	/// Takes an iterator and returns the iterator resulting from consuming it
	/// using this CanConsume counts.
	pub fn advance_iter<'a>(
		self,
		mut iter: impl Iterator<Item = &'a str> + Clone,
	) -> (Consumed, impl Iterator<Item = &'a str> + Clone)
	{
		let (consumed, first) = self.advance_iter_in_place(&mut iter);
		(consumed, first.into_iter().chain(iter))
	}
}

/// Like CanConsume except has been consumed.
/// `tokens` will be 1 if the last token was consumed completely
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Consumed
{
	/// The number of complete tokens consumed
	pub tokens: usize,

	// The number of bytes consumed from the last token
	pub chars: usize,
}

impl Consumed
{
	pub fn then(&self, next: &CanConsume) -> CanConsume
	{
		CanConsume {
			tokens: self.tokens + next.tokens,
			chars: if next.tokens == 0
			{
				self.chars + next.chars
			}
			else
			{
				next.chars
			},
		}
	}
}

/// Given to `Parser::parse`'s closure/function to allow for various ways of
/// resolve symbol addresses.
pub enum Resolve<'a>
{
	/// The absolute address of the given symbol
	Address(&'a str),

	/// The distance from the current address to the given symbol
	DistanceCurrent(&'a str),

	/// The distance from the first symbol to the second.
	///
	/// If the first symbol's address is highest, the result should be a
	/// negative distance.
	Distance(&'a str, &'a str),
}

pub trait Parser<'a>
{
	type Internal;

	const ALONE_LEFT: bool;
	const ALONE_RIGHT: bool;

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
	/// symbols. See `Resolve` for more.
	///
	/// The given iterator must produce tokens of only ASCII characters free of
	/// whitespace. Effectively, the iterator must behave as if it was produced
	/// by [`split_ascii_whitespace`](https://doc.rust-lang.org/std/primitive.str.html#method.split_ascii_whitespace)
	fn parse<I, F, B>(tokens: I, _: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32;

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

impl<'a> Parser<'a> for ()
{
	type Internal = ();

	const ALONE_LEFT: bool = false;
	const ALONE_RIGHT: bool = false;

	fn parse<I, F, B>(_: I, _: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		Ok(((), CanConsume::none()))
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

#[duplicate_item(
	typ;
	[u8]; [u16]; [u32]; [u64]; [u128];
	[i8]; [i16]; [i32]; [i64]; [i128];
)]
impl<'a> Parser<'a> for typ
{
	type Internal = typ;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		let value_string = tokens.next()
			.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
			// Extract digits from beginning
			.map(|t| t.splitn(2, |c| {
				!char::is_digit(c, 10) && (typ::MIN == 0 || (c != '-'))
			}).next().unwrap())?;
		value_string
			.parse()
			.map(|v| (v, CanConsume::chars(value_string.len())))
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

impl<'a, const SIZE: u32, const SIGNED: bool> Parser<'a> for Bits<SIZE, SIGNED>
{
	type Internal = Self;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		i32::parse(tokens, f).and_then(|(value, consumed)| {
			value.try_into().map_or(
				Err(ParseError::from_consumed(
					consumed.clone(),
					ParseErrorType::from_bits::<SIZE, SIGNED>(value as isize),
				)),
				|b| Ok((b, consumed)),
			)
		})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		i32::print(&internal.value, out)
	}
}

impl<'a, const SIZE: u32, const SIGNED: bool> Parser<'a> for Exclude<Bits<SIZE, SIGNED>, 0i32>
{
	type Internal = Self;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		Bits::<SIZE, SIGNED>::parse(tokens, f)
			.and_then(|(bits, consumed)| {
				if bits != Bits::zero()
				{
					Ok((bits, consumed))
				}
				else
				{
					Err(ParseError::from_consumed(
						consumed,
						ParseErrorType::OutOfBoundValue(0, 1, 255),
					))
				}
			})
			.map(|(bits, consumed)| (bits.into(), consumed))
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		let bits = internal.value().try_into().unwrap();
		Bits::<SIZE, SIGNED>::print(&bits, out)
	}
}

pub struct Implicit<P, const DEFAULT: i32>(P);
impl<'a, P, const DEFAULT: i32> Parser<'a> for Implicit<P, DEFAULT>
where
	P: Parser<'a>,
	P::Internal: TryFrom<i32> + Eq,
	<P::Internal as TryFrom<i32>>::Error: Debug,
{
	type Internal = <P as Parser<'a>>::Internal;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		match P::parse(tokens, f)
		{
			Ok((bits, consumed)) if bits != DEFAULT.try_into().unwrap() => Ok((bits, consumed)),
			Ok((_, consumed)) =>
			{
				Err(ParseError::from_consumed(
					consumed,
					ParseErrorType::Invalid("Must omit implicit value"),
				))
			},
			Err(_) => Ok((DEFAULT.try_into().unwrap(), CanConsume::none())),
		}
	}

	fn print_with_whitespace(
		internal: &Self::Internal,
		prev_alone: bool,
		out: &mut impl Write,
	) -> std::fmt::Result
	{
		if *internal != DEFAULT.try_into().unwrap()
		{
			if prev_alone && Self::ALONE_LEFT
			{
				out.write_char(' ')?;
			}
			P::print(internal, out)
		}
		else
		{
			Ok(())
		}
	}

	fn print(_: &Self::Internal, _: &mut impl Write) -> std::fmt::Result
	{
		unreachable!()
	}
}

pub struct Symbol();
impl<'a> Parser<'a> for Symbol
{
	type Internal = &'a str;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
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
			.map(|sym| (sym, CanConsume::chars(sym.len())))
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		let f = f.borrow();
		i32::parse::<_, F, _>(tokens.clone(), f)
			.or_else(|_| {
				Symbol::parse::<_, F, _>(tokens, f).map(|(symbol, consumed)| {
					let difference = f(Resolve::DistanceCurrent(symbol)) / 2;
					(difference - ((difference > 0) as i32), consumed)
				})
			})
			.and_then(|(value, consumed)| {
				value.try_into().map_or_else(
					|_| {
						Err(ParseError::from_consumed(
							consumed.clone(),
							ParseErrorType::from_bits::<SIZE, SIGNED>(value as isize),
						))
					},
					|b| Ok((b, consumed.clone())),
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		let f = f.borrow();
		Then::<Arrow, u16>::parse::<_, F, _>(tokens.clone(), f)
			.and_then(|(((), value), consumed)| {
				(value as i32).try_into().map_or_else(
					|_| {
						Err(ParseError::from_token(
							tokens.clone().next().unwrap().split_at(2).1,
							consumed.tokens,
							ParseErrorType::from_bits::<SIZE, false>(value as isize),
						))
					},
					|b| Ok((b, consumed.clone())),
				)
			})
			.or_else(|mut err| {
				let mut result = Then::<Arrow, Symbol>::parse::<_, F, _>(tokens.clone(), f)
					.and_then(|(((), sym1), consumed)| {
						let off1 = (f.borrow()(Resolve::DistanceCurrent(sym1)) / 2) - 1;
						if off1 < 0
						{
							Err(ParseError {
								start_token: consumed.tokens,
								start_idx: 2 * ((consumed.tokens == 0) as usize),
								end_token: consumed.tokens,
								end_idx: (2 * ((consumed.tokens == 0) as usize)) + sym1.len(),
								err_type: ParseErrorType::Invalid(
									"must be at or follow the instruction",
								),
							})
						}
						else
						{
							Ok(((sym1, off1), consumed))
						}
					});
				let mut next_branch_to = true;
				let mut next_result = result.clone();
				while let Ok(((sym1, offset), consumed)) = next_result
				{
					result = Ok(((sym1, offset), consumed.clone()));

					let (consumed, iter) = consumed.advance_iter(tokens.clone());
					next_result = Then::<Arrow, Symbol>::parse::<_, F, _>(iter, f).and_then(
						|(((), sym), consumed2)| {
							let next_consumed = consumed.then(&consumed2);

							if next_branch_to
							{
								Ok(((sym, offset), next_consumed))
							}
							else
							{
								let next_offset = f.borrow()(Resolve::Distance(sym1, sym)) / 2;
								if next_offset < 0
								{
									Err(ParseError {
										start_token: next_consumed.tokens
											+ ((next_consumed.chars > 0) as usize),
										start_idx: consumed.chars
											* ((consumed2.tokens == 0) as usize),
										end_token: next_consumed.tokens,
										end_idx: sym.len()
											+ (consumed.chars * ((consumed2.tokens == 0) as usize)),
										err_type: ParseErrorType::Invalid(
											"must refer to an address higher than the previous \
											 label in the chain",
										),
									})
								}
								else
								{
									Ok(((sym, offset + next_offset), next_consumed))
								}
							}
						},
					);
					next_branch_to = !next_branch_to;
				}
				result.and_then(|((_, offset), consumed)| {
					offset
						.try_into()
						.or({
							err.replace_if_further(&ParseError::from_consumed(
								consumed.clone(),
								ParseErrorType::from_bits::<SIZE, false>(offset as isize),
							));
							Err(err)
						})
						.map(|b| (b, consumed))
				})
			})
			.or_else(|err| {
				Arrow::parse::<_, F, _>(tokens.clone(), f)
					.and_then(|(_, consumed)| Ok((Bits::zero(), consumed)))
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		Then::<P1, Then<Comma, P2>>::parse(tokens, f)
			.map(|((left, ((), right)), consumed)| ((left, right), consumed))
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		let f = f.borrow();
		match P1::parse::<_, F, _>(tokens.clone(), f)
		{
			Ok((result1, can_consumed1)) =>
			{
				let (consumed1, iter) = can_consumed1.clone().advance_iter(tokens.clone());

				match P2::parse::<_, F, _>(iter, f)
				{
					// If P2 didn't consume anything, report the raw consumed of P1
					Ok((result2, con)) if con == CanConsume::none() =>
					{
						Ok(((result1, result2), can_consumed1))
					},
					Ok((result2, consumed2)) =>
					{
						Ok(((result1, result2), consumed1.then(&consumed2)))
					},
					Err(err) =>
					{
						Err(ParseError {
							start_token: consumed1.tokens + err.start_token,
							start_idx: err.start_idx
								+ ((err.start_token == 0) as usize * consumed1.chars),
							end_token: consumed1.tokens + err.end_token,
							end_idx: err.end_idx
								+ ((err.end_token == 0) as usize * consumed1.chars),
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		let f = f.borrow();
		let err1 = match P1::parse::<_, F, _>(tokens.clone(), f)
		{
			Ok((result, consumed)) =>
			{
				match result.try_into()
				{
					Ok(result) => return Ok((result, consumed)),
					_ =>
					{
						ParseError::from_consumed(
							consumed,
							ParseErrorType::InternalError(concat!(file!(), ':', line!())),
						)
					},
				}
			},
			Err(err) => err,
		};

		match P2::parse::<_, F, _>(tokens, f)
		{
			Ok((parsed, consumed)) =>
			{
				match parsed.try_into()
				{
					Ok(result) => Ok((result, consumed)),
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

/// Used to parse a specific static string instead of manually implementing
/// `Parser`.
///
/// To use, create an empty type and implement this trait in it, giving it the
/// string you want to parse as `WORD`.
/// Then use the type as the Parser.
pub trait Keyword
{
	const WORD: &'static str;
}
impl<'a, T: Keyword> Parser<'a> for T
{
	type Internal = ();

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		tokens
			.next()
			.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
			.and_then(|t| {
				if t.starts_with(T::WORD)
				{
					Ok(((), CanConsume::chars(T::WORD.len())))
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

duplicate! {
	[
		name	text;
		[High]	["High"];
		[Low]	["Low"];
		[Int]	["Int"];
		[Uint]	["Uint"];
	]
	pub struct name();
	impl Keyword for name
	{
		const WORD:&'static str = text;
	}
}

duplicate! {
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
		) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
		where
			I: Iterator<Item = &'a str> + Clone,
			B: Borrow<F>,
			F: Fn(Resolve) -> i32
		{
			tokens.next()
				.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
				.and_then(|t| if t.starts_with(text) {
					Ok(((), CanConsume::chars(text.len())))
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		match P::parse(tokens, f)
		{
			Ok((result, consumed)) => Ok((Some(result), consumed)),
			Err(_) => Ok((None, CanConsume::none())),
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		match P::parse(tokens, f)
		{
			Ok((_, consumed)) => Ok((true, consumed)),
			Err(_) => Ok((false, CanConsume::none())),
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		match P1::parse::<_, F, _>(tokens.clone(), f.borrow())
		{
			Ok((_, consumed)) => Ok((true, consumed)),
			Err(err1) =>
			{
				match P2::parse::<_, F, _>(tokens, f)
				{
					Ok((_, consumed)) => Ok((false, consumed)),
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		let (result, consumed) = P::parse(tokens, f)?;
		if let Ok(result) = result.try_into()
		{
			Ok((result, consumed))
		}
		else
		{
			Err(ParseError::from_consumed(
				consumed,
				ParseErrorType::InternalError(concat!(file!(), ':', line!())),
			))
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
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

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		let starts_with_symbol = Symbol::parse(tokens.clone(), |_: Resolve| 0).is_ok();
		let ((off1, off2), consumed) =
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
		value.try_into().map_or(
			Err(ParseError::from_consumed(
				consumed.clone(),
				ParseErrorType::from_bits::<7, true>(value as isize),
			)),
			|v| Ok(((v, off2), consumed)),
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

	fn parse<I, F, B>(mut tokens: I, _: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
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

				let value_error = Err(ParseError::from_consumed(
					CanConsume::chars(value_str.len()),
					ParseErrorType::UnexpectedChars("a power of 2"),
				));
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
							pow.try_into()
								.or(Err(ParseError::from_token(
									value_str,
									0,
									ParseErrorType::from_bits::<SIZE, false>(pow as isize),
								)))
								.map(|b| (b, CanConsume::chars(value_str.len())))
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

	fn parse<I, F, B>(mut tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
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
					Bits::<3, false>::parse(Some(&token[1..]).into_iter(), f)
						.map_err(|mut err| {
							err.start_idx += 1;
							err
						})
						.map(|(b, consumed)| ((signed, b), CanConsume::chars(consumed.chars + 1)))
				})
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		out.write_char(if internal.0 { 'i' } else { 'u' })?;
		Bits::<3, false>::print(&internal.1, out)
	}
}

// let parsed_ref = Then::<Symbol, Maybe<Then<Arrow, Symbol>>>::parse::<_, F,
// _>(next_token.clone().into_iter().chain(iter.clone()), f.borrow())
// .and_then(|((sym1, sym2), consumed2)|{
// if let Some((_, sym2)) = sym2 {
// Ok((f.borrow()(Resolve::Distance(sym1, sym2)), consumed2))
// } else {
// Ok((f.borrow()(Resolve::Address(sym1)), consumed2))
// }
// });
//

pub struct TypedConst<'a, const SIZE: u32>(PhantomData<&'a ()>);
impl<'a, const SIZE: u32> Parser<'a> for TypedConst<'a, SIZE>
{
	type Internal = BitsDyn<SIZE>;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		IntSize::parse::<_, F, _>(tokens.clone(), f.borrow()).and_then(
			|((signed, pow2), consumed)| {
				assert_eq!(consumed.tokens, 0);
				if SIZE >= 2u32.pow(pow2.value as u32)
				{
					let (consumed, tokens) = consumed.advance_iter(tokens);

					let parsed_ref =
						Then::<Then<Comma, Symbol>, Maybe<Then<Arrow, Symbol>>>::parse::<_, F, _>(
							tokens.clone(),
							f.borrow(),
						)
						.and_then(|(((_, sym1), sym2), consumed2)| {
							if let Some((_, sym2)) = sym2
							{
								Ok((f.borrow()(Resolve::Distance(sym1, sym2)), consumed2))
							}
							else
							{
								Ok((f.borrow()(Resolve::Address(sym1)), consumed2))
							}
						});

					if signed
					{
						parsed_ref
							.map(|(val, consumed2)| {
								(Bits::<SIZE, true>::try_from(val).unwrap().into(), consumed2)
							})
							.or_else(|_| {
								Then::<Comma, Bits<SIZE, true>>::parse(tokens, f)
									.map(|((_, b), consumed2)| (b.into(), consumed2))
							})
					}
					else
					{
						parsed_ref
							.map(|(val, consumed2)| {
								(
									Bits::<SIZE, false>::try_from(val).unwrap().into(),
									consumed2,
								)
							})
							.or_else(|_| {
								Then::<Comma, Bits<SIZE, false>>::parse(tokens, f)
									.map(|((_, b), consumed2)| (b.into(), consumed2))
							})
					}
					.map(|(b, consumed2)| (b, consumed.then(&consumed2)))
					.map_err(|err| {
						let consumed_tok = consumed.tokens > 0;
						ParseError {
							start_token: err.start_token + consumed_tok as usize,
							start_idx: if !consumed_tok && err.start_token == 0
							{
								err.start_idx + consumed.chars
							}
							else
							{
								err.start_idx
							},
							end_token: err.end_token + consumed_tok as usize,
							end_idx: if !consumed_tok && err.start_token == 0
							{
								err.end_idx + consumed.chars
							}
							else
							{
								err.end_idx
							},
							err_type: err.err_type,
						}
					})
				}
				else
				{
					Err(ParseError {
						start_token: 0,
						start_idx: 1,
						end_token: 0,
						end_idx: consumed.chars,
						// TODO: should handle higher powers of 2
						err_type: ParseErrorType::OutOfBoundValue(pow2.value as isize, 0, 0),
					})
				}
			},
		)
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		assert!(SIZE >= 8); // TODO: support higher bit lengths
		if let Ok(bits) = internal.clone().try_into()
		{
			CommaBetween::<IntSize, Bits<SIZE, true>>::print(
				&((true, 0i32.try_into().unwrap()), bits),
				out,
			)
		}
		else
		{
			CommaBetween::<IntSize, Bits<SIZE, false>>::print(
				&(
					(false, 0i32.try_into().unwrap()),
					internal.clone().try_into().unwrap(),
				),
				out,
			)
		}
	}
}

pub struct VecLength<'a>(PhantomData<&'a ()>);
impl<'a> Parser<'a> for VecLength<'a>
{
	type Internal = Bits<3, false>;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve) -> i32,
	{
		Pow2::<3>::parse(tokens.clone(), f)
			.and_then(|(value, consumed)| {
				if value.is_max()
				{
					Err(ParseError::from_consumed(
						consumed,
						ParseErrorType::OutOfBoundValue(value.value as isize, 0, 6),
					))
				}
				else
				{
					Ok((value, consumed))
				}
			})
			.or_else(|_| {
				tokens
					.next()
					.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
					.and_then(|t| {
						if t.starts_with('_')
						{
							Ok((Bits::get_min(), CanConsume::chars(1)))
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
