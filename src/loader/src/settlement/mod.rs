//! Settlement infrastructure for consolidating multiple SMF modules.
//!
//! A Settlement is a runtime container that:
//! - Merges code/data from multiple modules into contiguous regions
//! - Uses indirection tables for function/global access (enabling hot reload)
//! - Supports native library embedding (static) or loading (shared)
//! - Can be packaged as an executable

mod builder;
mod container;
mod native;
mod slots;
mod tables;

pub use builder::*;
pub use container::*;
pub use native::*;
pub use slots::*;
pub use tables::*;
