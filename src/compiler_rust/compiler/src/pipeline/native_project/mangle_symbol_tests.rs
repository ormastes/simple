use super::mangle_mir;
use crate::hir::TypeId;
use crate::mir::{MirFunction, MirInst, MirModule, VReg, Visibility};
use std::collections::{HashMap, HashSet};

fn function(name: &str) -> MirFunction {
    MirFunction::new(name.to_string(), TypeId::I64, Visibility::Private)
}

fn load(name: &str) -> MirInst {
    MirInst::GlobalLoad {
        dest: VReg(0),
        global_name: name.to_string(),
        ty: TypeId::I64,
    }
}

fn bind(module: &mut MirModule, suffixes: HashMap<String, Vec<String>>) {
    mangle_mir(
        module,
        "probe__ports",
        false,
        &HashMap::new(),
        &HashSet::new(),
        &HashMap::new(),
        &suffixes,
    );
}

fn reference_name(instruction: &MirInst) -> &str {
    match instruction {
        MirInst::GlobalLoad { global_name, .. } | MirInst::GlobalStore { global_name, .. } => global_name,
        _ => panic!("expected global function/value reference"),
    }
}

#[test]
fn local_function_values_resolve_before_ambiguous_imported_suffixes() {
    let mut module = MirModule::new();
    let mut caller = function("make_port");
    caller.blocks[0].instructions.push(load("_gpu"));
    caller.blocks[0].instructions.push(MirInst::GlobalStore {
        global_name: "_gpu".to_string(),
        value: VReg(0),
        ty: TypeId::I64,
    });
    module.functions = vec![function("_gpu"), caller];
    // Imported bindings also populate the per-module suffix index. A global
    // suffix map alone would leave the local suffix unique and miss the bug.
    mangle_mir(
        &mut module,
        "probe__ports",
        false,
        &HashMap::from([
            ("one_gpu".to_string(), "one___gpu".to_string()),
            ("two_gpu".to_string(), "two___gpu".to_string()),
        ]),
        &HashSet::new(),
        &HashMap::new(),
        &HashMap::from([(
            "_gpu".to_string(),
            vec!["one___gpu".to_string(), "two___gpu".to_string()],
        )]),
    );
    assert_eq!(module.functions[0].name, "probe__ports___gpu");
    for instruction in &module.functions[1].blocks[0].instructions {
        assert_eq!(reference_name(instruction), module.functions[0].name);
    }
}

#[test]
fn private_spl_function_definitions_keep_their_module_owner() {
    let mut module = MirModule::new();
    let mut caller = function("make_manifest");
    caller.blocks[0].instructions.push(load("spl_language_manifest"));
    module.functions = vec![function("spl_language_manifest"), caller];
    bind(&mut module, HashMap::new());
    assert_eq!(module.functions[0].name, "probe__ports__spl_language_manifest");
    assert_eq!(
        reference_name(&module.functions[1].blocks[0].instructions[0]),
        module.functions[0].name
    );
}

#[test]
fn local_rt_function_values_resolve_before_runtime_prefix_classification() {
    let mut module = MirModule::new();
    let mut caller = function("make_executor");
    caller.blocks[0].instructions.push(load("rt_hal_unavailable_spawn"));
    module.functions = vec![function("rt_hal_unavailable_spawn"), caller];
    bind(&mut module, HashMap::new());
    assert_eq!(module.functions[0].name, "probe__ports__rt_hal_unavailable_spawn");
    assert_eq!(
        reference_name(&module.functions[1].blocks[0].instructions[0]),
        module.functions[0].name
    );
}

#[test]
fn real_local_global_precedes_a_same_named_function() {
    let mut module = MirModule::new();
    // ABI globals are intentionally not in local_global_mangled. Ownership
    // still protects them from the newly module-owned private function name.
    module.globals.push(("spl_reserved".to_string(), TypeId::I64, true));
    module.local_globals.insert("spl_reserved".to_string());
    let mut caller = function("read_reserved");
    caller.blocks[0].instructions.push(load("spl_reserved"));
    module.functions = vec![function("spl_reserved"), caller];
    bind(&mut module, HashMap::new());
    assert_eq!(module.functions[0].name, "probe__ports__spl_reserved");
    assert_eq!(module.globals[0].0, "spl_reserved");
    assert_eq!(
        reference_name(&module.functions[1].blocks[0].instructions[0]),
        "spl_reserved"
    );
}

#[test]
fn explicit_exports_globals_and_extern_abi_symbols_remain_bare() {
    let mut module = MirModule::new();
    let mut exported = function("spl_exported");
    exported.attributes.push("export".to_string());
    let mut global = function("spl_global");
    global.attributes.push("global".to_string());
    let mut foreign = function("spl_ordered_key_cmp");
    foreign.blocks.clear();
    module.extern_fn_names.insert(foreign.name.clone());
    let mut caller = function("abi_refs");
    caller.blocks[0].instructions = vec![load("spl_exported"), load("spl_global"), load("spl_ordered_key_cmp")];
    module.functions = vec![exported, global, foreign, caller];
    bind(&mut module, HashMap::new());
    let expected = ["spl_exported", "spl_global", "spl_ordered_key_cmp"];
    for (index, name) in expected.iter().enumerate() {
        assert_eq!(module.functions[index].name, *name);
        assert_eq!(
            reference_name(&module.functions[3].blocks[0].instructions[index]),
            *name
        );
    }
}

#[test]
fn entry_main_keeps_the_canonical_spl_main_abi() {
    let mut module = MirModule::new();
    module.functions.push(function("main"));
    mangle_mir(
        &mut module,
        "probe",
        true,
        &HashMap::new(),
        &HashSet::new(),
        &HashMap::new(),
        &HashMap::new(),
    );
    assert_eq!(module.functions[0].name, "spl_main");
}

#[test]
fn actual_callback_fixture_function_metadata_does_not_shadow_lexical_owners() {
    use crate::hir::Lowerer;
    use crate::mir::lower_to_mir;
    use simple_parser::Parser;

    let source = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../../test/fixtures/native/symbol_owner_binding/probe/ports.spl");
    let text = std::fs::read_to_string(source).unwrap();
    let ast = Parser::new(&text).parse().unwrap();
    let hir = Lowerer::new().lower_module(&ast).unwrap();
    let mut mir = lower_to_mir(&hir).unwrap();
    for name in ["_gpu", "rt_hal_unavailable_spawn"] {
        assert!(mir.local_globals.contains(name), "real HIR registers function metadata");
        assert!(
            !mir.globals.iter().any(|(global, _, _)| global == name),
            "function metadata is not a data declaration"
        );
    }
    bind(&mut mir, HashMap::new());
    for name in ["_gpu", "rt_hal_unavailable_spawn"] {
        let owner = format!("probe__ports__{name}");
        assert!(mir.functions.iter().any(|function| function.name == owner));
        let loads: Vec<_> = mir
            .functions
            .iter()
            .flat_map(|function| &function.blocks)
            .flat_map(|block| &block.instructions)
            .filter_map(|instruction| match instruction {
                MirInst::GlobalLoad { global_name, .. } if global_name.ends_with(name) => Some(global_name),
                _ => None,
            })
            .collect();
        assert_eq!(loads.len(), 2, "real make_gpu_port/maybe_port must reference {name}");
        assert!(
            loads.iter().all(|target| *target == &owner),
            "actual callback refs: {loads:?}"
        );
    }
}

// ---- Sibling split-part facade calls (bug mangler_bare_extern_sibling_split_part) ----
//
// A free helper defined in one `_CamelCase/` split-part file and called from a
// sibling split-part file reaches the caller only through the parent facade's
// wildcard re-export, so use_map/import_map carry no entry for it. The only
// resolution path is the closure-wide suffix index; when the name is defined
// several times in the closure the mangler must pick the definition whose module
// path shares the longest prefix with the caller, and must never emit it bare.

const SIMD_CALLER: &str = "semantics__lint___SimdOpportunityLint__arithmetic_checks";
const SIMD_SIBLING: &str = "semantics__lint___SimdOpportunityLint__loop_analysis";

fn call(name: &str) -> MirInst {
    MirInst::Call {
        dest: None,
        target: crate::mir::CallTarget::Pure(name.to_string()),
        args: vec![],
    }
}

fn called_name(instruction: &MirInst) -> &str {
    match instruction {
        MirInst::Call { target, .. } => target.name(),
        _ => panic!("expected call"),
    }
}

/// Run `mangle_mir` for a caller in `prefix` that calls each of `callees`.
/// Returns (resolved call names, unresolved count).
fn mangle_calls(
    prefix: &str,
    callees: &[&str],
    ambiguous: &[&str],
    suffixes: &[(&str, Vec<&str>)],
) -> (Vec<String>, usize) {
    let mut module = MirModule::new();
    let mut caller = function("lint_simd_elementwise_add");
    caller.blocks[0].instructions = callees.iter().map(|c| call(c)).collect();
    module.functions = vec![caller];
    let ambiguous: HashSet<String> = ambiguous.iter().map(|s| s.to_string()).collect();
    let suffix_index: HashMap<String, Vec<String>> = suffixes
        .iter()
        .map(|(k, v)| (k.to_string(), v.iter().map(|s| s.to_string()).collect()))
        .collect();
    let unresolved = mangle_mir(
        &mut module,
        prefix,
        false,
        &HashMap::new(),
        &ambiguous,
        &HashMap::new(),
        &suffix_index,
    );
    let names = module.functions[0].blocks[0]
        .instructions
        .iter()
        .map(|i| called_name(i).to_string())
        .collect();
    (names, unresolved)
}

#[test]
fn ambiguous_private_helper_resolves_to_sibling_split_part() {
    let sibling = format!("{SIMD_SIBLING}___find_substr");
    let (names, unresolved) = mangle_calls(
        SIMD_CALLER,
        &["_find_substr"],
        &["_find_substr"],
        &[(
            "_find_substr",
            vec![
                "gc_async_mut__gpu__browser_engine__html_tokenizer___find_substr",
                sibling.as_str(),
                "tools__duplicate_check__math_utils___find_substr",
            ],
        )],
    );
    assert_eq!(names, vec![sibling]);
    assert_eq!(unresolved, 0);
}

#[test]
fn ambiguous_public_helper_resolves_to_sibling_split_part() {
    // Same shape as the private case but without the leading underscore: the
    // facade-crossing defect is not specific to `_`-prefixed names
    // (`run_test_api_server_with_inject` failed the same way).
    let sibling = format!("{SIMD_SIBLING}__strip_manifest_blocks");
    let (names, unresolved) = mangle_calls(
        SIMD_CALLER,
        &["strip_manifest_blocks"],
        &["strip_manifest_blocks"],
        &[(
            "strip_manifest_blocks",
            vec!["tools__coverage__manifest__strip_manifest_blocks", sibling.as_str()],
        )],
    );
    assert_eq!(names, vec![sibling]);
    assert_eq!(unresolved, 0);
}

#[test]
fn unique_sibling_helper_resolves_through_suffix_index() {
    let sibling = format!("{SIMD_SIBLING}__only_here");
    let (names, unresolved) = mangle_calls(
        SIMD_CALLER,
        &["only_here"],
        &[],
        &[("only_here", vec![sibling.as_str()])],
    );
    assert_eq!(names, vec![sibling]);
    assert_eq!(unresolved, 0);
}

#[test]
fn ambiguous_helper_without_a_closer_sibling_is_not_guessed() {
    // Two unrelated definitions, neither sharing a module prefix with the
    // caller: there is no sound pick, so the call must stay unresolved (and be
    // counted) rather than bind to an arbitrary owner.
    let (names, unresolved) = mangle_calls(
        "app__cli__main",
        &["_find_substr"],
        &["_find_substr"],
        &[(
            "_find_substr",
            vec!["lib__text___find_substr", "tools__dup__math___find_substr"],
        )],
    );
    assert_eq!(names, vec!["_find_substr".to_string()]);
    assert_eq!(unresolved, 1);
}

#[test]
fn ambiguous_helper_with_tied_siblings_is_not_guessed() {
    let (names, unresolved) = mangle_calls(
        SIMD_CALLER,
        &["_find_substr"],
        &["_find_substr"],
        &[(
            "_find_substr",
            vec![
                "semantics__lint___SimdOpportunityLint__loop_analysis___find_substr",
                "semantics__lint___SimdOpportunityLint__byte_checks___find_substr",
            ],
        )],
    );
    assert_eq!(names, vec!["_find_substr".to_string()]);
    assert_eq!(unresolved, 1);
}
