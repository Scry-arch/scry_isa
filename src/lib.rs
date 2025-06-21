//! This crate defines the Scry Instruction Set Architecture.
#![recursion_limit = "2048"]
#[cfg(feature = "quickcheck_arbitrary")]
/// Provides implementations of `quickcheck::Arbitrary` for testing with
/// `quickcheck`.
pub mod arbitrary;
mod assembly;
mod bits;
mod instructions;
mod matchers;

pub use assembly::*;
pub use bits::*;
pub use instructions::*;
pub use matchers::*;
