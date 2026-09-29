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
