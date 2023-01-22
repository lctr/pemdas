pub mod color;
pub mod grapheme;
pub(crate) mod lexicon;
pub mod style;
pub mod symbol;

pub use lexicon::{intern, lookup};
