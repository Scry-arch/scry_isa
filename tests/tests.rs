#[cfg(feature = "quickcheck_arbitrary")]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

mod instructions;
mod misc;
#[cfg(feature = "quickcheck_arbitrary")]
mod properties;
