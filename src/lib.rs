//! This crate defines the Scry Instruction Set Architecture.
mod matchers;
mod instructions;
mod assembly;

pub use matchers::Parser;
pub use instructions::*;

