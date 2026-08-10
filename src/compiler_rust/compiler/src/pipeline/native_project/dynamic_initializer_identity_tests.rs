use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Arc;

use object::{Object, ObjectSection, ObjectSymbol, SectionKind};

use super::compiler::{assign_native_dynamic_initializer_identity, compile_file_to_object};
use super::{ModuleImports, NativeProjectBuilder};
use crate::codegen::common_backend::{module_dynamic_init_symbol, module_init_symbol, module_prefix_from_path};
use crate::hir::{HirModule, Lowerer};
use crate::optimizations::NativeOptimizationLevel;

fn lower(source: &str) -> HirModule {
    let ast = simple_parser::Parser::new(source).parse().expect("parse fixture");
    let mut lowerer = Lowerer::new();
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    lowerer.lower_module(&ast).expect("lower fixture")
}

fn empty_imports() -> ModuleImports {
    ModuleImports {
        import_map: Arc::new(HashMap::new()),
        ambiguous_names: Arc::new(HashSet::new()),
        all_mangled: Arc::new(HashMap::new()),
        re_exports: Arc::new(HashMap::new()),
        trait_impls: Arc::new(HashMap::new()),
        vtable_type_owners: Arc::new(HashSet::new()),
        vtable_symbols: Arc::new(HashMap::new()),
        struct_defs: Arc::new(HashMap::new()),
        duplicate_struct_defs: Arc::new(HashMap::new()),
        enum_defs: Arc::new(HashMap::new()),
        enum_runtime_names: Arc::new(HashMap::new()),
        data_exports: Arc::new(HashSet::new()),
        fn_arities: Arc::new(HashMap::new()),
        fn_return_types: Arc::new(HashMap::new()),
        populate_global_struct_defs: false,
        populate_global_enum_defs: false,
    }
}

fn defined_global_symbols(object_bytes: &[u8]) -> HashSet<String> {
    let object = object::File::parse(object_bytes).expect("parse native object");
    object
        .symbols()
        .filter(|symbol| symbol.is_definition() && symbol.is_global())
        .filter_map(|symbol| symbol.name().ok().map(ToOwned::to_owned))
        .collect()
}

fn defined_symbol_section_kind(object_bytes: &[u8], name: &str) -> SectionKind {
    let object = object::File::parse(object_bytes).expect("parse native object");
    let symbol = object
        .symbols()
        .find(|symbol| symbol.is_definition() && symbol.name().ok() == Some(name))
        .unwrap_or_else(|| panic!("missing defined symbol `{name}`"));
    let section_index = symbol
        .section_index()
        .unwrap_or_else(|| panic!("symbol `{name}` has no data section"));
    object
        .section_by_index(section_index)
        .unwrap_or_else(|error| panic!("read section for `{name}`: {error}"))
        .kind()
}

#[test]
fn physical_prefix_qualifies_only_the_hir_synthetic_initializer() {
    let source = "fn make_value() -> i64:\n    return 11\nval runtime_value: i64 = make_value()\n";
    let mut left = lower(source);
    let mut right = lower(source);

    assign_native_dynamic_initializer_identity(&mut left, "alpha__shared").unwrap();
    assign_native_dynamic_initializer_identity(&mut right, "beta__shared").unwrap();

    let left_names: HashSet<&str> = left.functions.iter().map(|function| function.name.as_str()).collect();
    let right_names: HashSet<&str> = right.functions.iter().map(|function| function.name.as_str()).collect();
    assert!(left_names.contains("__module_init_alpha__shared_dynamic"));
    assert!(right_names.contains("__module_init_beta__shared_dynamic"));
    assert!(!left_names.contains("__module_init_dynamic"));
    assert!(!right_names.contains("__module_init_dynamic"));
}

#[test]
fn prequalified_source_initializer_is_preserved_and_collision_fails_closed() {
    let qualified = "__module_init_app__globals_dynamic";
    let mut prequalified = lower(&format!("fn {qualified}():\n    return\n"));
    assign_native_dynamic_initializer_identity(&mut prequalified, "app__globals").unwrap();
    assert!(prequalified.functions.iter().any(|function| function.name == qualified));

    let mut source_defined_raw = lower(
        "fn __module_init_dynamic():\n    return\nfn make_value() -> i64:\n    return 13\nval runtime_value: i64 = make_value()\n",
    );
    assign_native_dynamic_initializer_identity(&mut source_defined_raw, "app__globals").unwrap();
    assert!(source_defined_raw
        .functions
        .iter()
        .any(|function| function.name == "__module_init_dynamic" && function.span.is_some()));
    assert!(source_defined_raw
        .functions
        .iter()
        .any(|function| function.name == "__module_init_app__globals_dynamic" && function.span.is_none()));

    let mut collision = lower(&format!(
        "fn make_value() -> i64:\n    return 7\nval runtime_value: i64 = make_value()\nfn {qualified}():\n    return\n"
    ));
    let error = assign_native_dynamic_initializer_identity(&mut collision, "app__globals").unwrap_err();
    assert!(error.contains("destination `__module_init_app__globals_dynamic` already exists"));
    assert!(collision
        .functions
        .iter()
        .any(|function| function.name == "__module_init_dynamic" && function.span.is_none()));
}

#[test]
fn llvm_mangling_preserves_the_same_physical_initializer_identity() {
    let mut hir = lower("fn make_value() -> i64:\n    return 17\nval runtime_value: i64 = make_value()\n");
    let prefix = "pkg__same__physical";
    assign_native_dynamic_initializer_identity(&mut hir, prefix).unwrap();
    let mut mir = crate::mir::lower_to_mir(&hir).expect("lower MIR fixture");

    super::mangle::mangle_mir(
        &mut mir,
        prefix,
        false,
        &HashMap::new(),
        &HashSet::new(),
        &HashMap::new(),
        &HashMap::new(),
    );

    assert!(mir
        .functions
        .iter()
        .any(|function| function.name == "__module_init_pkg__same__physical_dynamic"));
    assert!(!mir
        .functions
        .iter()
        .any(|function| function.name == "__module_init_dynamic"));
}

#[test]
fn dotted_freestanding_initializer_uses_canonical_identity_and_replaces_the_redundant_hir_body() {
    let source = "fn make_value() -> i64:\n    return 23\nval runtime_value: i64 = make_value()\n";
    let mut ast = simple_parser::Parser::new(source).parse().expect("parse fixture");
    let prefix = "os__ui.render__shared";
    let qualified = module_dynamic_init_symbol(Some(prefix));
    super::module_global_init::inject_freestanding_module_global_init(&mut ast, prefix);
    let mut lowerer = Lowerer::new();
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let mut hir = lowerer.lower_module(&ast).expect("lower freestanding fixture");
    assert!(hir
        .functions
        .iter()
        .any(|function| function.name == "__module_init_dynamic"));
    assert!(hir.functions.iter().any(|function| function.name == qualified));
    assert!(!hir
        .functions
        .iter()
        .any(|function| function.name == "__module_init_os__ui_render__shared_dynamic"));

    assign_native_dynamic_initializer_identity(&mut hir, prefix).unwrap();

    assert!(!hir
        .functions
        .iter()
        .any(|function| function.name == "__module_init_dynamic"));
    assert_eq!(
        hir.functions
            .iter()
            .filter(|function| function.name == qualified)
            .count(),
        1
    );
}

#[cfg(not(target_os = "windows"))]
#[test]
fn two_same_basename_modules_link_and_run_each_runtime_global_initializer_exactly_once() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    if std::process::Command::new(&cc).arg("--version").output().is_err() {
        return;
    }

    let temp = tempfile::tempdir().unwrap();
    let source_root = temp.path().join("src");
    let left_path = source_root.join("alpha/shared.spl");
    let right_path = source_root.join("beta/shared.spl");
    std::fs::create_dir_all(left_path.parent().unwrap()).unwrap();
    std::fs::create_dir_all(right_path.parent().unwrap()).unwrap();
    let left_source = "var init_calls: i64 = 0\nfn make_value() -> i64:\n    init_calls = init_calls + 1\n    return 11\nval runtime_value: i64 = make_value()\nfn read_value() -> i64:\n    return runtime_value\nfn read_init_calls() -> i64:\n    return init_calls\n";
    let right_source = "var init_calls: i64 = 0\nfn make_value() -> i64:\n    init_calls = init_calls + 1\n    return 31\nval runtime_value: i64 = make_value()\nfn read_value() -> i64:\n    return runtime_value\nfn read_init_calls() -> i64:\n    return init_calls\n";
    std::fs::write(&left_path, left_source).unwrap();
    std::fs::write(&right_path, right_source).unwrap();

    let compile = |source: &str, path: &Path| {
        compile_file_to_object(
            source,
            path,
            temp.path(),
            &source_root,
            &source_root,
            std::slice::from_ref(&source_root),
            false,
            "cranelift",
            NativeOptimizationLevel::None,
            false,
            &empty_imports(),
        )
        .unwrap_or_else(|error| panic!("compile {}: {error}", path.display()))
    };
    let left_object = compile(left_source, &left_path);
    let right_object = compile(right_source, &right_path);
    let left_prefix = module_prefix_from_path(&left_path, &source_root);
    let right_prefix = module_prefix_from_path(&right_path, &source_root);
    assert_ne!(left_prefix, right_prefix);

    for (object, prefix) in [(&left_object, &left_prefix), (&right_object, &right_prefix)] {
        let symbols = defined_global_symbols(object);
        assert!(!symbols.contains("__module_init_dynamic"));
        assert!(symbols.contains(&format!("{}_dynamic", module_init_symbol(Some(prefix)))));
        assert!(symbols.contains(&module_init_symbol(Some(prefix))));
    }

    let left_object_path = temp.path().join("left.o");
    let right_object_path = temp.path().join("right.o");
    let driver_path = temp.path().join("driver.c");
    let executable = temp.path().join("probe");
    std::fs::write(&left_object_path, left_object).unwrap();
    std::fs::write(&right_object_path, right_object).unwrap();
    let object_paths = vec![right_object_path.clone(), left_object_path.clone()];
    let init_object = NativeProjectBuilder::new(temp.path().to_path_buf(), executable.clone())
        .generate_init_caller(temp.path(), &object_paths, None)
        .unwrap()
        .expect("generated aggregate initializer");
    std::fs::write(
        &driver_path,
        format!(
            "#include <stdint.h>\nextern void __simple_call_module_inits(void);\nextern int64_t {left_prefix}__read_value(void);\nextern int64_t {right_prefix}__read_value(void);\nextern int64_t {left_prefix}__read_init_calls(void);\nextern int64_t {right_prefix}__read_init_calls(void);\nint main(void) {{ __simple_call_module_inits(); return ({left_prefix}__read_value() == 11 && {right_prefix}__read_value() == 31 && {left_prefix}__read_init_calls() == 1 && {right_prefix}__read_init_calls() == 1) ? 0 : 1; }}\n",
        ),
    )
    .unwrap();

    let link = std::process::Command::new(&cc)
        .arg(&driver_path)
        .arg(&right_object_path)
        .arg(&left_object_path)
        .arg(&init_object)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        link.status.success(),
        "link failed: {}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = std::process::Command::new(&executable).output().unwrap();
    assert!(
        run.status.success(),
        "runtime initializers did not produce both values exactly once: status={:?} stderr={}",
        run.status.code(),
        String::from_utf8_lossy(&run.stderr)
    );
}

#[cfg(all(feature = "llvm", not(target_os = "windows")))]
#[test]
fn llvm_mixed_heap_and_dynamic_globals_run_the_dynamic_initializer_exactly_once_through_the_wrapper() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    if std::process::Command::new(&cc).arg("--version").output().is_err() {
        return;
    }

    let temp = tempfile::tempdir().unwrap();
    let source_root = temp.path().join("src");
    let source_path = source_root.join("mixed/owner.spl");
    std::fs::create_dir_all(source_path.parent().unwrap()).unwrap();
    let source = "extern fn probe_next() -> i64\nval values: [i64] = []\nval runtime_value: i64 = probe_next()\nfn read_value() -> i64:\n    return runtime_value\n";
    std::fs::write(&source_path, source).unwrap();

    let object = compile_file_to_object(
        source,
        &source_path,
        temp.path(),
        &source_root,
        &source_root,
        std::slice::from_ref(&source_root),
        false,
        "llvm",
        NativeOptimizationLevel::None,
        false,
        &empty_imports(),
    )
    .unwrap_or_else(|error| panic!("compile {} with LLVM: {error}", source_path.display()));
    let prefix = module_prefix_from_path(&source_path, &source_root);
    let wrapper = module_init_symbol(Some(&prefix));
    let dynamic = module_dynamic_init_symbol(Some(&prefix));
    let symbols = defined_global_symbols(&object);
    assert!(symbols.contains(&wrapper));
    assert!(symbols.contains(&dynamic));
    let runtime_value = format!("{prefix}__runtime_value");
    assert!(
        matches!(
            defined_symbol_section_kind(&object, &runtime_value),
            SectionKind::Data | SectionKind::UninitializedData | SectionKind::Common
        ),
        "dynamic initializer target `{runtime_value}` must be writable"
    );

    let object_path = temp.path().join("mixed.o");
    let driver_path = temp.path().join("driver.c");
    let executable = temp.path().join("probe");
    std::fs::write(&object_path, object).unwrap();
    let init_object = NativeProjectBuilder::new(temp.path().to_path_buf(), executable.clone())
        .generate_init_caller(temp.path(), std::slice::from_ref(&object_path), None)
        .unwrap()
        .expect("generated aggregate initializer");
    let generated_caller = std::fs::read_to_string(temp.path().join("_init_all.cpp")).unwrap();
    assert!(generated_caller.contains(&format!("if ({wrapper}) {wrapper}();")));
    assert!(!generated_caller.contains(&dynamic));
    std::fs::write(
        &driver_path,
        format!(
            "#include <stdint.h>\nstatic int64_t probe_calls = 0;\nint64_t probe_next(void) {{ probe_calls += 1; return 41; }}\nint64_t rt_array_new(int64_t capacity) {{ (void)capacity; return 0; }}\nextern void __simple_call_module_inits(void);\nextern int64_t {prefix}__read_value(void);\nint main(void) {{ __simple_call_module_inits(); return ({prefix}__read_value() == 41 && probe_calls == 1) ? 0 : 1; }}\n",
        ),
    )
    .unwrap();

    let link = std::process::Command::new(&cc)
        .arg(&driver_path)
        .arg(&object_path)
        .arg(&init_object)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        link.status.success(),
        "LLVM mixed initializer link failed: {}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = std::process::Command::new(&executable).output().unwrap();
    assert!(
        run.status.success(),
        "LLVM mixed initializer did not run exactly once: status={:?} stderr={}",
        run.status.code(),
        String::from_utf8_lossy(&run.stderr)
    );
}
