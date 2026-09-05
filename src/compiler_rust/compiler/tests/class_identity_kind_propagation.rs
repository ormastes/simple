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

// =============================================================================
// F1/S5 — the copy PRIMITIVE, and the kind-gated decision to emit it
// =============================================================================
//
// S3 (above) proved the kind reaches MIR. It changed no behaviour, because MIR
// had nothing to branch INTO: a sweep of the seed for struct_copy / copy_struct
// / deep_copy / StructCopy found only `runtime/src/value/core.rs` `deep_copy`,
// used by the parallel executor, and nothing in `mir/` or `codegen/` at all.
// There was no aggregate-copy operation in the seed's MIR.
//
// S5 introduces one — `MirInst::AggregateCopy` — with lowerings in BOTH the
// cranelift JIT (`codegen/instr/closures_structs.rs::compile_aggregate_copy`)
// and LLVM (`codegen/llvm/functions/objects.rs::compile_aggregate_copy`), over
// the tagged-heap-pointer struct ABI both backends already share.
//
// These tests assert the DECISION, not the machine code: that the instruction
// is emitted for a declared `struct` and NOT for a declared `class`. That is
// the half a wrong answer would silently invert, and it is the half the A–K
// corpus cannot localise (the corpus sees an end-to-end verdict, so it cannot
// say whether a regression came from the gate or the lowering).
//
// SABOTAGE CHECK: making `copy_if_value_type` (mir/lower/lowering_core.rs)
// return `src` unconditionally makes `value_type_binding_emits_aggregate_copy`
// fail; making it ignore `type_value_kinds` makes
// `identity_type_binding_never_emits_aggregate_copy` fail. If neither fails,
// this file is not measuring anything.

/// Same shape, same statements, only the declaration keyword differs — so the
/// keyword is the only thing that can explain a difference in emitted MIR.
const COPY_SITE_SOURCE: &str = r#"
struct SCell:
    n: i64

class BCell:
    n: i64

fn bind_struct() -> i64:
    val a = SCell(n: 1)
    val b = a
    return b.n

fn bind_class() -> i64:
    val a = BCell(n: 1)
    val b = a
    return b.n
"#;

fn aggregate_copies_in(mir: &simple_compiler::mir::MirModule, func_name: &str) -> Vec<Option<String>> {
    mir.functions
        .iter()
        .filter(|f| {
            f.name == func_name
                || f.name.ends_with(&format!("__{}", func_name))
                || f.name.ends_with(&format!(".{}", func_name))
        })
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.instructions.iter())
        .filter_map(|i| match i {
            simple_compiler::mir::MirInst::AggregateCopy { type_name, .. } => Some(type_name.clone()),
            _ => None,
        })
        .collect()
}

#[test]
fn value_type_binding_emits_aggregate_copy() {
    let hir = parse_and_lower(COPY_SITE_SOURCE);
    let mir = lower_to_mir(&hir, None).expect("MIR lowering failed");

    let copies = aggregate_copies_in(&mir, "bind_struct");
    assert!(
        copies.iter().any(|n| n.as_deref() == Some("SCell")),
        "binding a declared `struct` must emit an AggregateCopy of that struct \
         — without one, `val b = a` stores the same tagged heap pointer and the \
         two names alias (corpus case G). Emitted copies: {:?}",
        copies
    );
}

#[test]
fn identity_type_binding_never_emits_aggregate_copy() {
    let hir = parse_and_lower(COPY_SITE_SOURCE);
    let mir = lower_to_mir(&hir, None).expect("MIR lowering failed");

    let copies = aggregate_copies_in(&mir, "bind_class");
    assert!(
        copies.is_empty(),
        "binding a declared `class` must NOT be copied — copying an identity \
         type converts the class defect into its struct sibling, which is the \
         exact trap lane F1 exists to avoid. Emitted copies: {:?}",
        copies
    );
}

#[test]
fn the_two_declarations_diverge_in_emitted_mir() {
    // Stated as a RELATION, so a future change that made both sides copy (or
    // both alias) cannot pass by satisfying the two tests above in isolation.
    let hir = parse_and_lower(COPY_SITE_SOURCE);
    let mir = lower_to_mir(&hir, None).expect("MIR lowering failed");

    let struct_copies = aggregate_copies_in(&mir, "bind_struct").len();
    let class_copies = aggregate_copies_in(&mir, "bind_class").len();
    assert!(
        struct_copies > class_copies,
        "struct and class must not lower identically: struct emitted {} \
         AggregateCopy, class emitted {}",
        struct_copies,
        class_copies
    );
}

#[test]
fn unknown_types_are_not_copied() {
    // No declaration at all for the aggregate: `type_value_kinds` has no entry,
    // which means UNKNOWN. The gate must fail closed.
    let hir = parse_and_lower(
        r#"
fn bind_builtin() -> i64:
    val a = 7
    val b = a
    return b
"#,
    );
    let mir = lower_to_mir(&hir, None).expect("MIR lowering failed");
    assert!(
        aggregate_copies_in(&mir, "bind_builtin").is_empty(),
        "an UNKNOWN type must never be copied — absence is not value-semantics"
    );
}

// =============================================================================
// F1/S6 — the FOURTH copy site: struct PARAMETER binding (corpus case J)
// =============================================================================
//
// S5 closed struct-literal field init, local binding, field store, and return
// (cases F/G/H/I/K), but explicitly left one alias path open: an incoming
// struct-typed PARAMETER is caller-owned storage — a plain `fn f(a: SCell)`
// receives the same tagged heap pointer the caller holds, so a mutation to
// `a` inside `f` is visible to the caller. S6 closes that gap by copying a
// declared-value-type parameter into a private local before the body runs,
// gated by the identical `type_value_kinds` check `copy_if_value_type` already
// uses (`copy_param_if_value_type`, mir/lower/lowering_core.rs).
//
// SABOTAGE CHECK: making `copy_param_if_value_type` return early
// unconditionally (or gate on the wrong `type_value_kinds` entry) makes
// `struct_parameter_binding_emits_aggregate_copy` fail. If it does not, this
// test is not measuring anything.

const PARAM_SITE_SOURCE: &str = r#"
struct SCell:
    n: i64

class BCell:
    n: i64

fn take_struct(a: SCell) -> i64:
    return a.n

fn take_class(a: BCell) -> i64:
    return a.n

impl SCell:
    me bump():
        self.n = self.n + 1
"#;

#[test]
fn struct_parameter_binding_emits_aggregate_copy() {
    let hir = parse_and_lower(PARAM_SITE_SOURCE);
    let mir = lower_to_mir(&hir, None).expect("MIR lowering failed");

    let copies = aggregate_copies_in(&mir, "take_struct");
    assert!(
        copies.iter().any(|n| n.as_deref() == Some("SCell")),
        "binding a declared `struct` PARAMETER must emit an AggregateCopy \
         before the body runs — without one, the parameter aliases the \
         caller's storage (corpus case J). Emitted copies: {:?}",
        copies
    );
}

#[test]
fn class_parameter_binding_never_emits_aggregate_copy() {
    let hir = parse_and_lower(PARAM_SITE_SOURCE);
    let mir = lower_to_mir(&hir, None).expect("MIR lowering failed");

    let copies = aggregate_copies_in(&mir, "take_class");
    assert!(
        copies.is_empty(),
        "binding a declared `class` PARAMETER must NOT be copied — copying an \
         identity type converts the class defect into its struct sibling. \
         Emitted copies: {:?}",
        copies
    );
}

#[test]
fn mutable_struct_receiver_never_emits_aggregate_copy() {
    let hir = parse_and_lower(PARAM_SITE_SOURCE);
    let bump = hir
        .functions
        .iter()
        .find(|f| f.name == "bump" || f.name.ends_with("__bump") || f.name.ends_with(".bump"))
        .expect("fixture must lower SCell.bump into HIR");
    assert!(
        bump.params
            .first()
            .is_some_and(|param| param.name == "self" && param.is_mutable()),
        "a me-method self parameter must remain mutable through HIR lowering: {:?}",
        bump.params
    );
    let mir = lower_to_mir(&hir, None).expect("MIR lowering failed");

    assert!(
        mir.functions
            .iter()
            .any(|f| f.name == "bump" || f.name.ends_with("__bump") || f.name.ends_with(".bump")),
        "fixture must lower SCell.bump into MIR"
    );

    let copies = aggregate_copies_in(&mir, "bump");
    assert!(
        copies.is_empty(),
        "a mutable me receiver must alias its caller; copying it discards \
         every field update at method return. Emitted copies: {:?}",
        copies
    );
}

#[test]
fn struct_and_class_parameter_binding_diverge_in_emitted_mir() {
    let hir = parse_and_lower(PARAM_SITE_SOURCE);
    let mir = lower_to_mir(&hir, None).expect("MIR lowering failed");

    let struct_copies = aggregate_copies_in(&mir, "take_struct").len();
    let class_copies = aggregate_copies_in(&mir, "take_class").len();
    assert!(
        struct_copies > class_copies,
        "struct and class parameters must not lower identically: struct \
         emitted {} AggregateCopy, class emitted {}",
        struct_copies,
        class_copies
    );
}
