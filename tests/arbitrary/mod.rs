use quickcheck::{Arbitrary, Gen};
use std::fmt::Debug;

/// Represents the different ways separator character sequences (",", "=>",
/// etc.) can be in separate tokens
#[derive(Clone, Copy, Debug)]
pub enum SeparatorType
{
	/// The separator is at the end of a token with other text preceding it.
	AtEnd,
	/// The separator is at the start of a token with other text succeeding it.
	AtStart,
	/// The separator is in the middle of a token with text both preding and
	/// succeeding it.
	InMiddle,
	/// The separator is alone in the token, with no other text.
	Alone,
}
impl Arbitrary for SeparatorType
{
	fn arbitrary(g: &mut Gen) -> Self
	{
		use SeparatorType::*;
		*g.choose(&[AtEnd, AtStart, InMiddle, Alone]).unwrap()
	}
}
