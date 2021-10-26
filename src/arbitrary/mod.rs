use num_traits::PrimInt;
use quickcheck::{Arbitrary, Gen};

/// Generates arbitrary numbers within the range [low, high[.
fn gen_range<T: Arbitrary + PrimInt>(g: &mut Gen, low: T, high: T) -> T
{
	let base = T::arbitrary(g);
	let diff = high - low;
	let modulo = base % diff;
	modulo + if modulo < T::zero() { high } else { low }
}

mod instruction;
mod misc;

pub use instruction::*;
pub use misc::*;
