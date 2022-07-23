use duplicate::duplicate;
use scry_isa::{Bits, Exclude};
use std::convert::TryFrom;

#[test]
fn rejects_excluded()
{
	duplicate! {
		[size; [3]; [4]; [5];]
		duplicate!{
			[val; [0]; [1]; [2]; [3];]
			duplicate!{
				[sign; [true]; [false];]
				assert!(Exclude::<Bits<size,sign>,val>::try_from(val).is_err(),
					"size:{}, sign:{}, val:{}", size, sign, val);
			}
		}
	}
}
