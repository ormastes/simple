//! #6953: an enum variant's discriminant must be its OWN enum's declaration
//! index, independent of which other enums declared the same variant name and
//! in what order they were registered in this process.
//!
//! Shape of the incident (integ4 Stage 2, 2026-11-16): `OptimizationLevel`
//! declares `Speed` at 5 and `OptLevel` declares it at 2. The seed's
//! process-global, variant-name-keyed registry answered `Speed` with whatever
//! it saw first (pinned 5, or a name hash once ambiguous), so a natively built
//! `match level: case Speed:` in `mir_opt/mod.spl` tested a hash while the
//! constructor produced 5 -> "match expression exhausted".
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::HirModule;
use crate::module_resolver::ModuleResolver;
use crate::test_helpers::create_test_project;
use simple_parser::Parser;
use std::fs;

/// `backend_types.OptimizationLevel` shape: `Speed6953` at index 5.
const WIDE: &str = "enum Level6953:\n    NoOpt6953\n    Debug6953\n    Basic6953\n    Size6953\n    Standard6953\n    Speed6953\n    Aggressive6953\n";
/// `mir_opt.OptLevel` shape (same enum NAME, different order): `Speed6953` at 2.
const NARROW: &str = "enum Level6953:\n    NoOpt6953\n    Size6953\n    Speed6953\n    Aggressive6953\n";
/// A module that uses the WIDE enum, imported first by the entry.
const WIDE_USER: &str = "use wide.{Level6953}\n\nfn wide_probe() -> Level6953:\n    Level6953.Speed6953\n";

const ENTRY: &str = "use wide_user.{wide_probe}\nuse narrow.{Level6953}\n\n\
fn pick() -> Level6953:\n    Level6953.Speed6953\n\n\
fn rank_qualified(level: Level6953) -> i64:\n    match level:\n        case Level6953.NoOpt6953: 0\n        case Level6953.Size6953: 1\n        case Level6953.Speed6953: 2\n        case Level6953.Aggressive6953: 3\n\n\
fn rank_bare(level: Level6953) -> i64:\n    match level:\n        case NoOpt6953: 0\n        case Size6953: 1\n        case Speed6953: 2\n        case Aggressive6953: 3\n";

fn lower_entry(files: &[(&str, &str)], entry: &str) -> (HirModule, crate::mir::MirModule) {
    let dir = create_test_project();
    let src = dir.path().join("src");
    for (name, text) in files {
        fs::write(src.join(name), text).unwrap();
    }
    let ast = Parser::new(entry).parse().expect("parse entry");
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
    let hir = Lowerer::with_module_resolver(resolver, src.join("main.spl"))
        .lower_module(&ast)
        .expect("entry must lower to HIR");
    let mir = crate::mir::lower_to_mir(&hir).expect("entry must lower to MIR");
    (hir, mir)
}

/// Integer discriminants that a function's HIR match arms test, in arm order.
/// `rt_enum_check_variant(slot, enum_id, disc)` / `rt_enum_check_discriminant(slot, disc)`.
fn tested_discriminants(hir: &HirModule, function: &str) -> Vec<i64> {
    let body = format!(
        "{:?}",
        hir.functions
            .iter()
            .find(|f| f.name == function)
            .unwrap_or_else(|| panic!("function {function} not lowered"))
            .body
    );
    let mut found = Vec::new();
    for (marker, skip) in [("\"rt_enum_check_variant\"", 1usize), ("\"rt_enum_check_discriminant\"", 0usize)] {
        let mut rest = body.as_str();
        while let Some(at) = rest.find(marker) {
            rest = &rest[at + marker.len()..];
            let ints: Vec<i64> = rest
                .split("Integer(")
                .skip(1)
                .take(skip + 1)
                .map(|tail| tail[..tail.find(')').unwrap()].parse().unwrap())
                .collect();
            found.push((body.len() - rest.len(), ints[skip]));
        }
    }
    found.sort();
    found.into_iter().map(|(_, disc)| disc).collect()
}

fn pre_resolve_wide_order_in_this_process() {
    // Another module of the same build registered the WIDE order and a site
    // already asked for `Speed6953` by name before NARROW's declaration arrived.
    simple_runtime::value::register_enum_variants(
        ["NoOpt6953", "Debug6953", "Basic6953", "Size6953", "Standard6953", "Speed6953", "Aggressive6953"]
            .into_iter(),
    );
    let _ = simple_runtime::value::hash_variant_discriminant("Speed6953");
}

#[test]
fn match_arms_test_the_owning_enums_declared_indexes() {
    pre_resolve_wide_order_in_this_process();
    let (hir, _mir) = lower_entry(
        &[("wide.spl", WIDE), ("narrow.spl", NARROW), ("wide_user.spl", WIDE_USER)],
        ENTRY,
    );
    assert_eq!(tested_discriminants(&hir, "rank_qualified"), vec![0, 1, 2, 3]);
    assert_eq!(tested_discriminants(&hir, "rank_bare"), vec![0, 1, 2, 3]);
}

/// `case Copy(d) | Move(d):` over a subject whose variant names are also
/// declared, at other indexes, by a sibling enum (`MirInst` vs the many
/// `Copy`/`Move` declarers in the compiler). The arm test resolved the owner
/// through the subject type, but the per-alternative BINDING guard was lowered
/// with an erased slot type and fell back to the name-keyed registry.
const OR_BINDING: &str = "enum Inst6953:\n    Copy6953(v: i64)\n    Move6953(v: i64)\n\n\
enum Shadow6953:\n    Nop6953\n    Pad6953\n    Copy6953(v: i64)\n    Move6953(v: i64)\n\n\
fn dest_of(inst: Inst6953) -> i64:\n    match inst:\n        case Copy6953(d) | Move6953(d): d\n";

#[test]
fn or_pattern_binding_guards_test_the_subjects_declared_indexes() {
    let (hir, _mir) = lower_entry(&[], OR_BINDING);
    let mut tested = tested_discriminants(&hir, "dest_of");
    tested.sort();
    assert_eq!(tested, vec![0, 0, 1, 1], "arm test + binding guard, each for Copy6953(0) and Move6953(1)");
}

#[test]
fn constructor_carries_the_owning_enums_declared_index_into_mir() {
    pre_resolve_wide_order_in_this_process();
    let (_hir, mir) = lower_entry(
        &[("wide.spl", WIDE), ("narrow.spl", NARROW), ("wide_user.spl", WIDE_USER)],
        ENTRY,
    );
    let pick = mir.functions.iter().find(|f| f.name == "pick").expect("pick lowered");
    let carried: Vec<u32> = pick
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
        .filter_map(|inst| match inst {
            crate::mir::MirInst::EnumUnit { variant_name, discriminant, .. } if variant_name == "Speed6953" => {
                Some(*discriminant)
            }
            _ => None,
        })
        .collect();
    assert_eq!(carried, vec![2], "construction must agree with the match arms' owner index");
}

/// `case Wrap(Copy(d) | Move(d)):` -- the or-pattern sits in a PAYLOAD slot,
/// so its binding guard must be typed by the payload field type, not erased.
const NESTED_OR_BINDING: &str = "enum Inst6953:\n    Copy6953(v: i64)\n    Move6953(v: i64)\n\n\
enum Shadow6953:\n    Nop6953\n    Pad6953\n    Copy6953(v: i64)\n    Move6953(v: i64)\n\n\
enum Box6953:\n    Wrap6953(inner: Inst6953)\n\n\
fn inner_of(b: Box6953) -> i64:\n    match b:\n        case Wrap6953(Copy6953(d) | Move6953(d)): d\n";

#[test]
fn nested_or_pattern_binding_guards_use_the_payload_field_type() {
    let (hir, _mir) = lower_entry(&[], NESTED_OR_BINDING);
    let tested = tested_discriminants(&hir, "inner_of");
    assert!(!tested.is_empty(), "nested or-pattern must be tested");
    assert!(
        tested.iter().all(|disc| (0..2).contains(disc)),
        "every test must use a declared index (Wrap6953=0, Copy6953=0, Move6953=1), got {tested:?}"
    );
}

/// `backend_types.OptimizationLevel` vs `mir_opt.OptLevel`: DIFFERENTLY named
/// enums sharing `Speed6953` at 5 and 2 -- the actual integ4 pair.
const OPTIMIZATION_LEVEL: &str = "enum OptimizationLevel6953:\n    None6953\n    Debug6953\n    Basic6953\n    Size6953\n    Standard6953\n    Speed6953\n    Aggressive6953\n";
const OPT_LEVEL: &str = "enum OptLevel6953:\n    NoOpt6953\n    Size6953\n    Speed6953\n    Aggressive6953\n";
const TWO_NAMES_ENTRY: &str = "use backend_types.{OptimizationLevel6953}\nuse mir_opt.{OptLevel6953}\n\n\
fn backend_speed() -> OptimizationLevel6953:\n    OptimizationLevel6953.Speed6953\n\n\
fn opt_speed() -> OptLevel6953:\n    OptLevel6953.Speed6953\n\n\
fn pass_rank(level: OptLevel6953) -> i64:\n    match level:\n        case NoOpt6953: 0\n        case Size6953: 1\n        case Speed6953: 2\n        case Aggressive6953: 3\n";

#[test]
fn differently_named_enums_sharing_a_variant_keep_their_own_indexes() {
    pre_resolve_wide_order_in_this_process();
    let (hir, mir) = lower_entry(
        &[("backend_types.spl", OPTIMIZATION_LEVEL), ("mir_opt.spl", OPT_LEVEL)],
        TWO_NAMES_ENTRY,
    );
    assert_eq!(tested_discriminants(&hir, "pass_rank"), vec![0, 1, 2, 3]);
    let carried = |function: &str| -> Vec<u32> {
        mir.functions
            .iter()
            .find(|f| f.name == function)
            .unwrap_or_else(|| panic!("{function} lowered"))
            .blocks
            .iter()
            .flat_map(|block| block.instructions.iter())
            .filter_map(|inst| match inst {
                crate::mir::MirInst::EnumUnit { discriminant, .. } => Some(*discriminant),
                _ => None,
            })
            .collect()
    };
    assert_eq!(carried("backend_speed"), vec![5]);
    assert_eq!(carried("opt_speed"), vec![2]);
}

/// native_project's merged-name guard: a same-named enum seeded from the
/// global (union) table and marked merged must never answer an index, while
/// the same shape unmarked answers its declared index.
#[test]
fn merged_global_enum_never_answers_an_index() {
    use crate::hir::{HirType, TypeRegistry};
    let union = HirType::Enum {
        name: "Level6953".to_string(),
        variants: ["NoOpt6953", "Debug6953", "Size6953", "Speed6953"].iter().map(|v| (v.to_string(), None)).collect(),
        generic_params: vec![],
        is_generic_template: false,
        type_bindings: std::collections::HashMap::new(),
    };
    let mut registry = TypeRegistry::new();
    let id = registry.register_named("Level6953".to_string(), union);
    assert_eq!(registry.owned_or_unique_variant_discriminant(id, Some("Level6953"), "Speed6953"), Some(3));
    registry.mark_merged_enum(id);
    assert_eq!(registry.owned_or_unique_variant_discriminant(id, Some("Level6953"), "Speed6953"), None);
    assert_eq!(registry.owned_or_unique_variant_discriminant(crate::hir::TypeId::ANY, None, "Speed6953"), None);
}

/// `TraceLevel` (80.driver/trace_config.spl) declares `None` at 0. A user
/// enum's `None` is NOT the builtin Option's 1.
const TRACE: &str = "enum Trace6953:\n    None\n    Functions6953\n";

fn install_interpreter_enum(source: &str) {
    let ast = Parser::new(source).parse().expect("parse enum");
    for item in ast.items {
        if let simple_parser::Node::Enum(def) = item {
            crate::interpreter::GLOBAL_ENUMS.with(|cell| cell.borrow_mut().insert(def.name.clone(), std::sync::Arc::new(def)));
        }
    }
}

fn interp_enum(enum_name: &str, variant: &str) -> crate::value::Value {
    crate::value::Value::Enum { enum_name: enum_name.to_string(), variant: variant.to_string(), payload: None }
}

/// An interpreter-fallback fn returning `OptLevel.Speed` through
/// `compile_interp_call`: the bridge must box the OWNER's index, which the
/// native `case Speed:` tests.
#[test]
fn interpreter_bridge_boxes_the_owning_enums_declared_index() {
    pre_resolve_wide_order_in_this_process();
    install_interpreter_enum(NARROW);
    install_interpreter_enum(TRACE);
    let boxed = crate::runtime_bridge::value_to_runtime(&interp_enum("Level6953", "Speed6953"));
    assert_eq!(simple_runtime::value::rt_enum_discriminant(boxed), 2);
    let boxed = crate::runtime_bridge::value_to_runtime(&interp_enum("Trace6953", "None"));
    assert_eq!(simple_runtime::value::rt_enum_discriminant(boxed), 0, "user `None` is its owner's index");
    let boxed = crate::runtime_bridge::value_to_runtime(&interp_enum("Option", "None"));
    assert_eq!(simple_runtime::value::rt_enum_discriminant(boxed), 1, "builtin Option.None keeps its ABI value");
}

#[test]
fn interpreter_rt_enum_discriminant_answers_the_owning_enums_declared_index() {
    use crate::interpreter::interpreter_extern::enum_sffi::rt_enum_discriminant_fn;
    pre_resolve_wide_order_in_this_process();
    install_interpreter_enum(NARROW);
    install_interpreter_enum(TRACE);
    assert_eq!(rt_enum_discriminant_fn(&[interp_enum("Level6953", "Speed6953")]).unwrap(), crate::value::Value::Int(2));
    assert_eq!(rt_enum_discriminant_fn(&[interp_enum("Trace6953", "None")]).unwrap(), crate::value::Value::Int(0));
}

/// `.is_ok()` on a USER enum that declares `Ok` must test that enum's index,
/// not the builtin Result's 0.
const USER_OK: &str = "enum Probe6953:\n    Pending6953\n    Ok\n    Err\n\n\
fn probe_ok(p: Probe6953) -> bool:\n    p.is_ok()\n";

#[test]
fn is_ok_on_a_user_enum_tests_its_own_declared_index() {
    let (_hir, mir) = lower_entry(&[], USER_OK);
    let function = mir.functions.iter().find(|f| f.name == "probe_ok").expect("probe_ok lowered");
    let mut consts: Vec<i64> = function
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
        .filter_map(|inst| match inst {
            crate::mir::MirInst::ConstInt { value, .. } => Some(*value),
            _ => None,
        })
        .collect();
    consts.sort();
    assert_eq!(consts, vec![0, 1], "enum id wildcard 0 + Probe6953.Ok's declared index 1");
}
