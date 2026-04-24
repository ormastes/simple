//! Rust-seed `UnitRegistry` — mirrors the pure-Simple `UnitRegistry` at
//! `src/compiler/30.types/units/unit_registry.spl`.
//!
//! Built lazily on first use by scanning `src/unit/simple-lang/**/*.spl` for
//! `class <Name>` files with `static fn symbol() -> "..."`,
//! `static fn kind() -> "..."`, `static fn scale_to_base() -> N.M`,
//! `static fn base_unit() -> "..."` (and optionally `numerator()` /
//! `denominator()` for composites). Used by the Rust seed semantic pass to
//! resolve `60_kmph`-style suffixed literals and dimension-signature lookups
//! before the legacy `Unit family 'X' not found` error fires.
//!
//! Composition-only; no inheritance.

pub mod registry;

pub use registry::{
    convert, dimensions_match, ensure_loaded, lookup, lookup_by_dimensions, populate_thread_local_state,
    UnitEntry, UnitRegistry,
};
