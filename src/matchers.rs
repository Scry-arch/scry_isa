use crate::{Alu2OutputVariant, BitValue, Bits, BitsDyn, Exclude, Type};
use duplicate::{duplicate, duplicate_item};
use petgraph::{
	algo::dijkstra::dijkstra,
	graph::{Graph, NodeIndex},
	Direction,
};
use std::{
	borrow::Borrow,
	collections::HashMap,
	convert::{TryFrom, TryInto},
	fmt::{Debug, Write},
	iter::once,
	marker::PhantomData,
};

/// The type of error parsing encountered.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ParseErrorType<'a>
{
	/// Couldn't resolve symbol
	UnknownSymbol,

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

	/// Two references of unequal offsets were found.
	///
	/// 0. The offset of the first reference
	/// 0. The offset of the second reference
	/// 0. The nodes of the first reference
	/// 0. The nodes of the second reference
	UnequalReference(u32, u32, Vec<ReferenceNode<'a>>, Vec<ReferenceNode<'a>>),

	/// An invalid reference was given
	///
	/// 0. The node index that is the source of the error (if it can be
	///    identified
	/// 0. The nodes of the relevant reference
	InvalidReference(Option<u32>, Vec<ReferenceNode<'a>>),

	/// Token stream ended unexpectedly.
	EndOfStream,

	/// Internal Error that shouldn't propagate outside the crate.
	///
	/// Please file a bug report with the given string referring to where in the
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
	// Create error pointing to the given token, with the given token and index char
	// starting points
	pub fn from_token(
		token: &str,
		token_idx: usize,
		char_idx: usize,
		err_type: ParseErrorType<'a>,
	) -> Self
	{
		Self {
			start_token: token_idx,
			start_idx: char_idx,
			end_token: token_idx,
			end_idx: char_idx + token.len(),
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

	/// Extracts the source of this error from the given iterator.
	/// The iterator must be in the same state as when given to whatever
	/// returned this error.
	pub fn extract_from_iter(&self, iter: impl Iterator<Item = &'a str> + Clone) -> String
	{
		let mut result = String::new();

		let mut iter = iter.skip(self.start_token);

		if self.end_token > self.start_token
		{
			result.push_str(&iter.next().unwrap()[self.start_idx..]);

			for _ in 0..(self.end_token - self.start_token - 1)
			{
				result.push(' ');
				result.push_str(iter.next().unwrap())
			}

			result.push(' ');
			result.push_str(&iter.next().unwrap()[..self.end_idx]);
		}
		else
		{
			result.push_str(&iter.next().unwrap()[self.start_idx..self.end_idx]);
		}
		result
	}
}

/// Represents how many tokens and characters a parsing consumed.
///
/// If less than 1 token was consumed, `tokens` will be 0, while `chars` will
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
	/// characters weren't). If the iterator is to be used for further parsing,
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
	pub fn none() -> Self
	{
		Self {
			tokens: 0,
			chars: 0,
		}
	}

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

	// Advance error position based on this consumed and whether the last
	// token was partially consumed
	pub fn advance_err(&self, err: &mut ParseError)
	{
		if err.start_token == 0
		{
			err.start_idx += self.chars;
			err.end_idx += self.chars;
		}
		err.start_token += self.tokens;
		err.end_token += self.tokens;
	}
}

/// Given to `Parser::parse`'s closure/function to allow for various ways of
/// resolve symbol addresses.
#[derive(Debug)]
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>;

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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
	{
		let error_type =
			ParseErrorType::UnexpectedChars("a symbol that start with a letter, '-', '_', or '.'");
		tokens
			.next()
			.ok_or_else(|| ParseError::from_token("", 0, 0, ParseErrorType::EndOfStream))
			.and_then(|t| {
				if t.starts_with(char::is_numeric)
				{
					Err(ParseError::from_token(t, 0, 0, error_type.clone()))
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
					Err(ParseError::from_token(t, 0, 0, error_type))
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
	{
		let f = f.borrow();
		i32::parse::<_, F, _>(tokens.clone(), f)
			.or_else(|_| {
				Symbol::parse::<_, F, _>(tokens, f).and_then(|(symbol, consumed)| {
					f(Resolve::DistanceCurrent(symbol))
						.map(|distance| {
							let difference = distance / 2;
							(difference - ((difference > 0) as i32), consumed.clone())
						})
						.map_err(|_| {
							ParseError::from_consumed(consumed, ParseErrorType::UnknownSymbol)
						})
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

/// Defines the types of nodes of references.
/// E.g. in "=>sym1=>|=>sym2=>1" "sym1", "|", "sym2" and "1" are nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReferenceNode<'a>
{
	/// A node representing a position where a function call's argument are
	/// given, I.e. "=>|"
	CallArgFlag,

	/// A node representing a symbol. I.e. "=>sym1"
	Symbol(&'a str),

	/// A node representing an integer offset from the previous node. I.e. "=>3"
	Offset(i32),
}

#[derive(Debug)]
pub enum ReferenceNodeParser<'a>
{
	/// A node representing a position where a function call's argument are
	/// given, I.e. "=>|"
	CallArgFlag,

	/// A node representing a symbol. I.e. "=>sym1"
	Symbol(&'a str),

	/// A node representing an integer offset from the previous node. I.e. "=>3"
	Offset(i32),

	/// A node representing a branching the reference. I.e. "=>(target1,
	/// target)"
	Branch(ReferenceDAG<'a>),
}

impl<'a> Parser<'a> for ReferenceNodeParser<'a>
{
	type Internal = Self;

	const ALONE_LEFT: bool = false;
	const ALONE_RIGHT: bool = false;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
	{
		let f = f.borrow();

		/// We have some errors below that are more "important" than others.
		/// Using this enum allows us to identify them and propagate them.
		/// E.g. unknown symbol errors should be preferred to the generic error
		/// saying a node is expected.
		///
		/// The Primary error are expected to be propagated to instead of any
		/// secondary errors
		enum ErrLevel<E>
		{
			Primary(E),
			Secondary(E),
		}
		impl<E> ErrLevel<E>
		{
			fn is_primary(&self) -> bool
			{
				match self
				{
					ErrLevel::Primary(_) => true,
					ErrLevel::Secondary(_) => false,
				}
			}

			fn get(self) -> E
			{
				match self
				{
					ErrLevel::Primary(e) | ErrLevel::Secondary(e) => e,
				}
			}
		}
		trait ErrorLevels<T, E>
		{
			/// Converts a normal parse result into one with error levels.
			///
			/// If true is given, the error is converted to a primary error
			fn priority_error(self, prio: bool) -> Result<T, ErrLevel<E>>;
		}
		impl<T, E> ErrorLevels<T, E> for Result<T, E>
		{
			fn priority_error(self, prio: bool) -> Result<T, ErrLevel<E>>
			{
				match self
				{
					Ok(t) => Ok(t),
					Err(e) =>
					{
						Err(
							if prio
							{
								ErrLevel::Primary(e)
							}
							else
							{
								ErrLevel::Secondary(e)
							},
						)
					},
				}
			}
		}

		// Accept pipe as call argument signifier
		Pipe::parse::<_, F, _>(tokens.clone(), f)
			.map(|(_, consumed)| (ReferenceNodeParser::CallArgFlag, consumed))
			.priority_error(false)

			// Accept positive integer as manual offset
			.or_else(|_| {
				u16::parse::<_, F, _>(tokens.clone(), f)
					.map(|(val, consumed)| (ReferenceNodeParser::Offset(val as i32), consumed))
			})
			.priority_error(false)

			.or_else(|_| {

				// Accept a symbol
				Symbol::parse::<_, F, _>(tokens.clone(), f)
					.priority_error(false)
					.map_or_else(

						// If not a symbol try accepting a branch within parentheses
						|_|{
							// We need to call ReferenceDAGParser to parse the branched references
							// However, it calls ReferenceNode for parsing already, resulting
							// In an infinite type checking recursion. To avoid this, we need to
							// use dynamic dispatch with the token iterator to break the recursion.
							// However, since it needs Clone, and that would mean I is not object-safe,
							// we use 'dyn_clone' to create an object safe version of I that can be boxed.
							// See here: https://stackoverflow.com/a/50785654/8171453
							use dyn_clone::{clone_trait_object, DynClone};
							trait CloneableIterator<'b>: Iterator<Item = &'b str> + DynClone {}
							impl<'b, T: Iterator<Item = &'b str> + DynClone> CloneableIterator<'b> for T {}
							clone_trait_object!(<'b> CloneableIterator<'b>);

							// We don't use one big "Then<..>" parse because we need to capture
							// exact consumes for the two branches. So, we do everything manually
							ParenLeft::parse::<_, F, _>(tokens.clone(), f)
								.priority_error(false)
								.and_then(move|(_, left_consume)|{
									let (left_consumed, tokens2) = left_consume.advance_iter(tokens.clone());
									let tokens2_box: Box<dyn CloneableIterator<'a>> = Box::new(tokens2);
									ReferenceDAGParser::<false>::parse::<_, F, _>(tokens2_box, f)
										.and_then(|(ref1, ref1_consume)|{
											Ok((tokens, ref1, left_consumed.then(&ref1_consume)))
										})
										.map_err(|mut err| {
											left_consumed.advance_err(&mut err);
											err
										})
										.priority_error(true)
								})
								.and_then(|(tokens, ref_node, consume)| {
									let (par_ref1_consumed, tokens3) = consume.advance_iter(tokens.clone());
									Comma::parse::<_, F, _>(tokens3, f)
										.and_then(|(_, comma_consume)| {
											Ok((tokens, ref_node, par_ref1_consumed.then(&comma_consume)))
										})
										.map_err(|mut err| {
											par_ref1_consumed.advance_err(&mut err);
											err
										})
										.priority_error(true)
								})
								.and_then(|(tokens, mut ref_dag, consume)| {
									let (left_ref1_comma_consumed, tokens4) = consume.advance_iter(tokens.clone());
									let tokens4_boxed: Box<dyn CloneableIterator<'a>> = Box::new(tokens4);
									ReferenceDAGParser::<false>::parse::<_, F, _>(tokens4_boxed, f)
										.and_then(|(ref2, ref2_consume)|{
											let _ = ref_dag.add_ref_dag(None, &ref2);

											Ok((tokens, ref_dag, left_ref1_comma_consumed.then(&ref2_consume)))
										})
										.map_err(|mut err| {
											left_ref1_comma_consumed.advance_err(&mut err);
											err
										})
										.priority_error(true)
								})
								// Ensure the right parenthesis is present
								.and_then(|(tokens, ref_dag, consume)| {
									let (consumed, tokens2) = consume.advance_iter(tokens.clone());
									ParenRight::parse::<_, F, _>(tokens2, f)
										.map(|(_, consume2)| (ReferenceNodeParser::Branch(ref_dag), consumed.then(&consume2)))
										.map_err(|mut err| {
											consumed.advance_err(&mut err);
											err
										})
										.priority_error(true)
								})
						},

						// Ensure symbol is known
						|(sym, consumed)|{
							f(Resolve::Address(sym)).map_err(|_| {
								ParseError::from_consumed(
									consumed.clone(),
									ParseErrorType::UnknownSymbol,
								)
							}).priority_error(true)?;

							Ok((ReferenceNodeParser::Symbol(sym), consumed))
						}
					)
			})
			.map_err(|err| {
				if err.is_primary() {
					err.get()
				} else {
					ParseError::from_no_span(ParseErrorType::UnexpectedChars("'|', '(', unsigned integer, or symbol"))
				}
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		use ReferenceNodeParser::*;
		let msg = match internal
		{
			CallArgFlag => "|".into(),
			Offset(x) => format!("{}", x),
			Symbol(sym) => format!("{}", sym),
			Branch(dag) => format!("{:?}", dag),
		};
		out.write_str(msg.as_str())
	}
}

/// Represents all the distinct paths in a reference.
///
/// These paths are most often a single list, e.g., "=>sym1=>sym2".
/// However, using multi-pathing, these can become trees or DAGs.
/// E.g. "=>sym1=>(sym2, sym3)" or "=>sym1=>(sym2, sym3)=>sym4"
#[derive(Debug)]
pub struct ReferenceDAG<'a>
{
	/// Holds the nodes and edges of the reference DAG
	///
	/// Included are the CanConsume for error reporting. It takes the start of
	/// the reference as baseline and reaches just before the given node
	graph: Graph<ReferenceNode<'a>, ()>,

	/// The root of the DAG. Should always be [ReferenceNode::Root]
	roots: Vec<NodeIndex>,
}

impl<'a> ReferenceDAG<'a>
{
	/// Creates a new, empty reference DAG, with a root
	fn new() -> Self
	{
		Self {
			graph: Graph::new(),
			roots: vec![],
		}
	}

	/// Add a path link
	fn add_compound_link(
		&mut self,
		source: Option<NodeIndex>,
		target: &ReferenceNodeParser<'a>,
	) -> impl Iterator<Item = NodeIndex>
	{
		match target
		{
			ReferenceNodeParser::Branch(ref_dag) =>
			{
				Box::new(self.add_ref_dag(source, ref_dag)) as Box<dyn Iterator<Item = NodeIndex>>
			},
			n =>
			{
				let new_node = match n
				{
					ReferenceNodeParser::CallArgFlag => ReferenceNode::CallArgFlag,
					ReferenceNodeParser::Offset(x) => ReferenceNode::Offset(*x),
					ReferenceNodeParser::Symbol(sym) => ReferenceNode::Symbol(*sym),
					n => unreachable!("unexpected reference node: {:?}", n),
				};

				Box::new(self.add_link(source, new_node))
			},
		}
	}

	/// Add a path link
	fn add_link(
		&mut self,
		source: Option<NodeIndex>,
		target: ReferenceNode<'a>,
	) -> impl Iterator<Item = NodeIndex>
	{
		let target_node = self.graph.add_node(target);

		if let Some(source) = source
		{
			assert!(self.graph.node_weight(source).is_some());
			self.graph.add_edge(source, target_node, ());
		}
		else
		{
			self.roots.push(target_node);
		}

		Box::new(once(target_node))
	}

	fn add_ref_dag(
		&mut self,
		source: Option<NodeIndex>,
		target: &ReferenceDAG<'a>,
	) -> impl Iterator<Item = NodeIndex>
	{
		let mut leaves = vec![];
		target.all_references_list().for_each(|path| {
			let mut last = source;
			for node in path.map(|idx| target.graph.node_weight(idx).unwrap())
			{
				last = Some(self.add_link(last, *node).next().unwrap());
			}
			leaves.push(last.unwrap());
		});

		leaves.into_iter()
	}

	/// Returns the root of the DAG
	fn get_roots(&self) -> impl Iterator<Item = NodeIndex> + '_
	{
		self.roots.iter().cloned()
	}

	#[allow(dead_code)]
	fn all_leaves(&self, source: NodeIndex) -> impl Iterator<Item = NodeIndex> + '_
	{
		let leaves = self.graph.externals(Direction::Outgoing);
		let paths: HashMap<NodeIndex, _> = dijkstra(&self.graph, source, None, |_| 1);
		leaves.filter(move |l| paths.contains_key(l))
	}

	/// Returns all distinct lists of references in the DAG.
	///
	/// E.g., given "=>sym1=>(sym2, sym3)" returns "[=>sym1=>sym2,
	/// =>sym1=>sym3]"
	fn all_references_list(&self) -> impl Iterator<Item = impl Iterator<Item = NodeIndex>> + '_
	{
		let leaves = self.graph.externals(Direction::Outgoing);
		leaves
			.clone()
			.flat_map(move |l| {
				self.get_roots()
					.flat_map(move |root| {
						petgraph::algo::simple_paths::all_simple_paths::<
							Vec<_>,
							&Graph<ReferenceNode, ()>,
						>(&self.graph, root, l, 0, None)
					})
					.map(|v| v.into_iter())
			})
			.chain(
				// 1-node paths will not produce a path in the above all_simple_paths call, so add
				// them here as their own path
				leaves.filter_map(|l| {
					if self.get_roots().find(|r| *r == l).is_some()
					{
						Some(vec![l].into_iter())
					}
					else
					{
						None
					}
				}),
			)
	}

	/// Returns the calculated offset of the reference.
	///
	/// If the distinct reference lists do not share the same offset, returns an
	/// error. May also return errors if calculating the offset results in an
	/// error. E.g. if a list is not valid.
	fn calculate_reference_offset<'b, B, F>(
		&self,
		f: B,
		self_consume: CanConsume,
	) -> Result<i32, ParseError<'b>>
	where
		'a: 'b,
		B: Borrow<F>,
		F: Fn(Resolve<'b>) -> Result<i32, &'b str>,
	{
		let f = f.borrow();
		let mut offset_result: Option<(_, Vec<&ReferenceNode>)> = None;

		for ref_list in self.all_references_list()
		{
			let path = ref_list
				.map(|n| self.graph.node_weight(n).unwrap())
				.collect::<Vec<_>>();
			let offset = path
				.iter()
				.enumerate()
				.fold(
					Ok((0, false, None)),
					|acumulate: Result<(i32, bool, Option<&str>), ParseError>, (node_idx, node)| {
						if let Err(err) = acumulate
						{
							Err(err)
						}
						else
						{
							let (offset, branch_to, last_symbol) = acumulate.unwrap();
							use ReferenceNode::*;
							Ok(match node
							{
								CallArgFlag => (offset + 1, branch_to, last_symbol),
								Symbol(s) =>
								{
									let additional = if !branch_to
									{
										let (resolve, sub) = if let Some(last_sym) = last_symbol
										{
											(Resolve::Distance(last_sym, s), 0)
										}
										else
										{
											(Resolve::DistanceCurrent(s), 1)
										};
										let distance = f(resolve).map_err(|_| {
											ParseError::from_consumed(
												self_consume.clone(),
												ParseErrorType::InternalError(
													"ReferenceDag contains unknown symbol.",
												),
											)
										})?;
										if distance < 0
										{
											Err(ParseError::from_consumed(
												self_consume.clone(),
												ParseErrorType::InvalidReference(
													Some(node_idx as u32),
													path.iter().cloned().cloned().collect(),
												),
											))?
										}
										(distance / 2) - sub
									}
									else
									{
										0
									};
									(offset + additional, !branch_to, Some(s))
								},
								Offset(x) => (offset + x, branch_to, last_symbol),
							})
						}
					},
				)?
				.0;

			if let Some((prev_off, prev_path)) = &offset_result
			{
				if offset != *prev_off
				{
					Err(ParseError::from_consumed(
						self_consume.clone(),
						ParseErrorType::UnequalReference(
							*prev_off as u32,
							offset as u32,
							prev_path.into_iter().cloned().cloned().collect(),
							path.into_iter().cloned().collect(),
						),
					))?;
				}
			}
			else
			{
				offset_result = Some((offset, path));
			}
		}
		Ok(offset_result.map(|(off, _)| off).unwrap_or(0))
	}
}

pub struct ReferenceDAGParser<const INIT_ARROW: bool>();
impl<'a, const INIT_ARROW: bool> Parser<'a> for ReferenceDAGParser<INIT_ARROW>
{
	type Internal = ReferenceDAG<'a>;

	const ALONE_LEFT: bool = false;
	const ALONE_RIGHT: bool = false;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
	{
		let f = f.borrow();

		let mut ref_dag = ReferenceDAG::<'a>::new();

		let parse_node = |tokens,
		                  ref_dag: &mut ReferenceDAG<'a>,
		                  prev_nodes: &Vec<NodeIndex>,
		                  prev_consume: Consumed,
		                  with_arrow| {
			if with_arrow
			{
				Then::<Arrow, ReferenceNodeParser>::parse::<_, F, _>(tokens, f)
					.map(|((_, node), consumed)| (node, consumed))
			}
			else
			{
				ReferenceNodeParser::parse::<_, F, _>(tokens, f)
			}
			.and_then(move |(node, consumed)| {
				let consumed_clone = consumed.clone();

				let prev_nodes = if prev_nodes.is_empty()
				{
					vec![None]
				}
				else
				{
					prev_nodes
						.iter()
						.map(|prev_node| Some(prev_node.clone()))
						.collect()
				};

				Ok((
					prev_nodes
						.into_iter()
						.flat_map(move |prev_node| ref_dag.add_compound_link(prev_node, &node))
						.collect::<Vec<_>>(),
					consumed_clone,
				))
			})
			.map_err(|mut err| {
				prev_consume.advance_err(&mut err);
				err
			})
		};

		// At least one "=>__" must be parsed
		let (mut prev_nodes, mut can_consume) = match parse_node(
			CanConsume::none().advance_iter(tokens.clone()).1,
			&mut ref_dag,
			&vec![],
			Consumed::none(),
			INIT_ARROW,
		)
		{
			Ok((nodes, consumed)) => (nodes, consumed),
			Err(err) =>
			{
				// Accept lone arrow as "=>0", but only if not followed by "(", which means
				// there is a branch
				if let (true, Ok((_, consumed)), Err(_)) = (
					INIT_ARROW,
					Arrow::parse::<_, F, _>(tokens.clone(), f),
					Then::<Arrow, ParenLeft>::parse::<_, F, _>(tokens, f),
				)
				{
					return Ok((ref_dag, consumed));
				}
				else
				{
					return Err(err);
				}
			},
		};

		// Any number of additional "=>___" may be parsed
		loop
		{
			let (consumed, tokens) = can_consume.clone().advance_iter(tokens.clone());
			(prev_nodes, can_consume) =
				match parse_node(tokens, &mut ref_dag, &prev_nodes, consumed.clone(), true)
				{
					Ok((p, c)) => (p, consumed.then(&c)),
					Err(err) =>
					{
						// If an unknown symbol was found, return as hard error
						if err.err_type == ParseErrorType::UnknownSymbol
						{
							return Err(err);
						}
						break;
					},
				}
		}
		Ok((ref_dag, can_consume))
	}

	fn print(_: &Self::Internal, _: &mut impl Write) -> std::fmt::Result
	{
		todo!()
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
	{
		let f = f.borrow();
		ReferenceDAGParser::<true>::parse::<_, F, _>(tokens.clone(), f).and_then(
			|(ref_dag, consumed)| {
				ref_dag
					.calculate_reference_offset::<_, F>(f, consumed.clone())
					.and_then(|value| {
						Bits::try_from(value).map_or_else(
							|_| {
								Err(ParseError::from_consumed(
									consumed.clone(),
									ParseErrorType::from_bits::<SIZE, false>(value as isize),
								))
							},
							|b| Ok((b, consumed.clone())),
						)
					})
			},
		)
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		[Base]	["Base"];
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
		[Pipe]	["|"]		[false];
		[ParenLeft]	["("]		[false];
		[ParenRight]	[")"]		[false];
		[BrackLeft]	["["]		[false];
		[BrackRight]	["]"]		[false];
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
			F: Fn(Resolve<'a>) -> Result<i32, &'a str>
		{
			tokens.next()
				.ok_or(ParseError::from_no_span(ParseErrorType::EndOfStream))
				.and_then(|t| if t.starts_with(text) {
					Ok(((), CanConsume::chars(text.len())))
				} else {
					Err(ParseError::from_token(
						t,
						0,0,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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

/// Parses using the given parser and then calls try_into in the result to get T
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
	{
		let starts_with_symbol = Symbol::parse(tokens.clone(), |_: Resolve| Ok(0)).is_ok();
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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

pub struct TypeMatcher<'a>(PhantomData<&'a ()>);
impl<'a> Parser<'a> for TypeMatcher<'a>
{
	type Internal = Bits<4, false>;

	const ALONE_LEFT: bool = true;
	const ALONE_RIGHT: bool = true;

	fn parse<I, F, B>(mut tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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
						0,
						ParseErrorType::UnexpectedChars("integer scalar size"),
					))
				}
				.and_then(|signed| {
					Bits::<2, false>::parse(Some(&token[1..]).into_iter(), f)
						.map_err(|mut err| {
							err.start_idx += 1;
							err.end_idx += 1;
							err
						})
						.map(|(b, consumed)| ((signed, b), CanConsume::chars(consumed.chars + 1)))
				})
				.and_then(|((signed, size), consumed)| {
					if signed
					{
						Type::Int(size.value as u8)
					}
					else
					{
						Type::Uint(size.value as u8)
					}
					.try_into()
					.map(|t| (t, consumed))
					.map_err(|_| {
						ParseError::from_token(
							token,
							0,
							1,
							ParseErrorType::OutOfBoundValue(size.value as isize, 0, 3),
						)
					})
				})
			})
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		let (signed, size) = match (*internal).try_into().unwrap()
		{
			Type::Int(x) => (true, x),
			Type::Uint(x) => (false, x),
		};

		out.write_char(if signed { 'i' } else { 'u' })?;
		Bits::<2, false>::print(&(size as i32).try_into().unwrap(), out)
	}
}

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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
	{
		Then::<TypeMatcher, Comma>::parse::<_, F, _>(tokens.clone(), f.borrow()).and_then(
			|((ty, _), consumed)| {
				let ty: Type = ty.try_into().unwrap();
				if SIZE >= ty.size() as u32
				{
					let (consumed, tokens) = consumed.advance_iter(tokens.clone());
					Then::<Symbol, Maybe<Then<Arrow, Symbol>>>::parse::<_, F, _>(
						tokens.clone(),
						f.borrow(),
					)
					.and_then(|((sym1, sym2), consumed2)| {
						f.borrow()(
							if let Some((_, sym2)) = sym2
							{
								Resolve::Distance(sym1, sym2)
							}
							else
							{
								Resolve::Address(sym1)
							},
						)
						.map(|addr| (addr, consumed2.clone()))
						.map_err(|_| {
							ParseError::from_consumed(consumed2, ParseErrorType::UnknownSymbol)
						})
					})
					.map(|(val, consumed2)| {
						(
							BitsDyn::<SIZE>::try_from((ty.is_signed_int(), val))
								.unwrap()
								.into(),
							consumed2,
						)
					})
					.or_else(|err1| {
						// Value is wrong, create sensible error by trying to parse
						// again, guaranteeing an error
						if ty.is_signed_int()
						{
							Bits::<SIZE, true>::parse(tokens, f)
								.map(|(b, consumed2)| (b.into(), consumed2))
						}
						else
						{
							Bits::<SIZE, false>::parse(tokens, f)
								.map(|(b, consumed2)| (b.into(), consumed2))
						}
						.or_else(|err2| {
							Err(match (&err1.err_type, &err2.err_type)
							{
								(
									ParseErrorType::UnknownSymbol,
									ParseErrorType::UnexpectedChars(_),
								) => err1,
								_ => err2,
							})
						})
					})
					.map(|(b, consumed2)| (b, consumed.then(&consumed2)))
					.map_err(|mut err| {
						consumed.advance_err(&mut err);
						err
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
						err_type: ParseErrorType::OutOfBoundValue(ty.size_pow2() as isize, 0, 0),
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
			CommaBetween::<TypeMatcher, Bits<SIZE, true>>::print(
				&(Type::Int(0).try_into().unwrap(), bits),
				out,
			)
		}
		else
		{
			CommaBetween::<TypeMatcher, Bits<SIZE, false>>::print(
				&(
					Type::Uint(0).try_into().unwrap(),
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
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
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

pub struct MemIndex<'a>(PhantomData<&'a ()>);
impl<'a> Parser<'a> for MemIndex<'a>
{
	type Internal = Bits<5, false>;

	const ALONE_LEFT: bool = false;
	const ALONE_RIGHT: bool = false;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
	{
		Then::<BrackLeft, Then<Bits<5, false>, BrackRight>>::parse(tokens.clone(), f)
			.and_then(|(value, consumed)| Ok((value.1 .0, consumed)))
	}

	fn print(internal: &Self::Internal, out: &mut impl Write) -> std::fmt::Result
	{
		out.write_char('[')?;
		Bits::<5, false>::print(internal, out)?;
		out.write_char(']')
	}
}

/// Parses a valueless prefix before parsing the value
pub struct Prefix<'a, P0: 'a + Parser<'a, Internal = ()>, P: 'a + Parser<'a>>(
	PhantomData<&'a (P0, P)>,
);
impl<'a, P0: 'a + Parser<'a, Internal = ()>, P: 'a + Parser<'a>> Parser<'a> for Prefix<'a, P0, P>
{
	type Internal = P::Internal;

	const ALONE_LEFT: bool = P0::ALONE_LEFT;
	const ALONE_RIGHT: bool = P::ALONE_RIGHT;

	fn parse<I, F, B>(tokens: I, f: B) -> Result<(Self::Internal, CanConsume), ParseError<'a>>
	where
		I: Iterator<Item = &'a str> + Clone,
		B: Borrow<F>,
		F: Fn(Resolve<'a>) -> Result<i32, &'a str>,
	{
		Then::<P0, P>::parse(tokens, f).map(|(value, consumed)| (value.1, consumed))
	}

	fn print_with_whitespace(
		internal: &Self::Internal,
		prev_alone: bool,
		out: &mut impl Write,
	) -> std::fmt::Result
	{
		P0::print_with_whitespace(&(), prev_alone, out)?;
		P::print_with_whitespace(&internal, P::ALONE_RIGHT, out)
	}

	fn print(internal: &Self::Internal, out: &mut impl std::fmt::Write) -> std::fmt::Result
	{
		P0::print(&(), out)?;
		P::print_with_whitespace(&internal, P::ALONE_RIGHT, out)
	}
}
