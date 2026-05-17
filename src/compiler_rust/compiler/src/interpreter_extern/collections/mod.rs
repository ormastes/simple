//! Collections FFI functions for the interpreter
//!
//! This module re-exports from the four collection-kind sub-modules.
//! Split by kind: hashmap, hashset, btreemap, btreeset.
//! Note: prescribed split names (list/dict/tuple/set) were adjusted because
//! this file contains HashMap/HashSet/BTreeMap/BTreeSet, not list/tuple types.

pub mod collections_hashmap;
pub mod collections_hashset;
pub mod collections_btreemap;
pub mod collections_btreeset;

pub use collections_hashmap::*;
pub use collections_hashset::*;
pub use collections_btreemap::*;
pub use collections_btreeset::*;

/// Clear all compiler-side collection registries between test runs.
pub fn clear_collection_registries() {
    collections_hashmap::clear_hashmap_registry();
    collections_hashset::clear_hashset_registry();
    collections_btreemap::clear_btreemap_registry();
    collections_btreeset::clear_btreeset_registry();
}
