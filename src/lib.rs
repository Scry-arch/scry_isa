//! This crate defines the Scry Instruction Set Architecture.
#![recursion_limit = "1024"]
mod assembly;
mod instructions;
mod matchers;

pub use instructions::*;
pub use matchers::*;
