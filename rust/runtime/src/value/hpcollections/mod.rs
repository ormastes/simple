//! High-performance collections using Rust std::collections.
//!
//! This module provides FFI bindings to Rust's standard library collections,
//! offering significantly better performance than the basic RuntimeDict.
//!
//! - HashMap: O(1) average-case operations vs O(n) for RuntimeDict
//! - BTreeMap: O(log n) operations with ordered iteration
//! - HashSet/BTreeSet: Efficient set operations
//!
//! All collections use a registry pattern to store actual Rust collections,
//! with RuntimeValue handles referencing them.

pub mod btreemap;
pub mod btreeset;
pub mod hashmap;
pub mod hashset;

// Re-export all FFI functions
pub use btreemap::*;
pub use btreeset::*;
pub use hashmap::*;
pub use hashset::*;
