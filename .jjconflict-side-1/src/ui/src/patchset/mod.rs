//! PatchSet - Reactive update operations
//!
//! Defines the operations for updating the UI tree incrementally.

mod ops;
mod diff;
mod subtree;

pub use ops::*;
pub use diff::*;
pub use subtree::*;
