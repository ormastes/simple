//! F1/S3 — the struct-vs-class DECLARATION KIND must survive HIR and MIR lowering.
//!
//! Background. `struct` = value semantics, `class` = identity semantics. The
//! parser knows which is which (`ast::ClassDef::is_value_type`, set at
//! `parser/src/types_def/mod.rs:109` for `struct` and `:232` for `class`), but
//! HIR lowering funnels BOTH declarations into the same `HirType::Struct` —
//! there is no `HirType::Class`. The kind was therefore discarded at
//! `hir/lower/type_registration.rs`, and MIR and both backends had nothing to
//! branch on. That is the root cause behind the whole class-identity corpus:
//! the seed JIT aliases structs (cases F–K) and the seed interpreter copies
//! classes (cases A–E), because neither can tell the two apart.
//!
//! These tests are the S3 oracle. They assert the kind is (a) recorded, (b)
//! recorded CORRECTLY per declaration form, and (c) still present after MIR
//! lowering — which is where S5's copy-vs-alias branch will read it.
//!
//! SABOTAGE CHECK: flipping the `true` at `register_struct` (or the
//! `c.is_value_type` at `register_class`) to a constant makes
//! `struct_and_class_kinds_are_distinct_in_hir` fail. If it does not, this file
//! is not measuring anything.
//!
//! Corpus and staging: doc/03_plan/ui/perf/f1_class_identity_kind_propagation_plan_2026-08-09.md

mod common;

use common::{lower_to_mir, parse_and_lower};

/// One `struct` and one `class`, same shape, so the ONLY thing that can explain
/// a difference in the recorded kind is the declaration keyword.
const SOURCE: &str = r#"
struct SCell:
    n: i64

class BCell:
    n: i64
"#;

#[test]
fn struct_and_class_kinds_are_distinct_in_hir() {
    let hir = parse_and_lower(SOURCE);

    assert_eq!(
        hir.type_is_value_kind("SCell"),
        Some(true),
        "a `struct` declaration must be recorded as a VALUE type; \
         type_value_kinds = {:?}",
        hir.type_value_kinds
    );
    assert_eq!(
        hir.type_is_value_kind("BCell"),
        Some(false),
        "a `class` declaration must be recorded as an IDENTITY type; \
         type_value_kinds = {:?}",
        hir.type_value_kinds
    );

    // The whole point is that the two are DISTINGUISHABLE. Asserting each value
    // separately would still pass if a future refactor made both constant in
    // the same direction only for one of the two names, so state the relation
    // itself.
    assert_ne!(
        hir.type_is_value_kind("SCell"),
        hir.type_is_value_kind("BCell"),
        "struct and class must not collapse to the same kind — collapsing them \
         is exactly the defect S3 exists to fix"
    );
}

#[test]
fn unregistered_names_report_unknown_not_value_type() {
    let hir = parse_and_lower(SOURCE);

    // Absence must read as "unknown", never as "value type". Consumers gate on
    // `Some(true)`; if a missing entry defaulted to value-semantics, every
    // builtin and every imported-but-unlowered aggregate would silently start
    // being copied, converting the class defect into its struct sibling.
    assert_eq!(hir.type_is_value_kind("NoSuchType"), None);
    assert_eq!(hir.type_is_value_kind("i64"), None);
}

#[test]
fn kind_survives_mir_lowering() {
    let hir = parse_and_lower(SOURCE);
    let mir = lower_to_mir(&hir, None).expect("MIR lowering failed");

    // MIR is where S5 reads the kind to choose copy-vs-alias for aggregate
    // binding and field stores. HIR-only propagation would be useless there.
    assert_eq!(
        mir.type_is_value_kind("SCell"),
        Some(true),
        "struct kind lost between HIR and MIR; type_value_kinds = {:?}",
        mir.type_value_kinds
    );
    assert_eq!(
        mir.type_is_value_kind("BCell"),
        Some(false),
        "class kind lost between HIR and MIR; type_value_kinds = {:?}",
        mir.type_value_kinds
    );
}

#[test]
fn actor_is_an_identity_type() {
    // Actors lower through `register_class` with `is_value_type: false`
    // (hir/lower/module_lowering/module_pass.rs). They are message-passing
    // reference types, so copying one would break its mailbox identity.
    let hir = parse_and_lower(
        r#"
actor Counter:
    n: i64
"#,
    );
    assert_eq!(hir.type_is_value_kind("Counter"), Some(false));
}
