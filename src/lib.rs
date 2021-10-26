//! This crate defines the Scry Instruction Set Architecture.
#![recursion_limit = "1024"]
#[cfg(feature = "quickcheck_arbitrary")]
/// Provides implementations of `quickcheck::Arbitrary` for testing with
/// `quickcheck`.
pub mod arbitrary;
mod assembly;
mod instructions;
mod matchers;

pub use instructions::*;
pub use matchers::*;
