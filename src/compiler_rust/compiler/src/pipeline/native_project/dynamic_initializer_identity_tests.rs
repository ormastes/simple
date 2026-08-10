use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Arc;

use object::{Object, ObjectSymbol};

use super::compiler::{assign_native_dynamic_initializer_identity, compile_file_to_object};
use super::{ModuleImports, NativeProjectBuilder};
use crate::codegen::common_backend::{module_init_symbol, module_prefix_from_path};
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

    let mut source_defined_raw = lower("fn __module_init_dynamic():\n    return\n");
    assign_native_dynamic_initializer_identity(&mut source_defined_raw, "app__globals").unwrap();
    assert!(source_defined_raw
        .functions
        .iter()
        .any(|function| function.name == "__module_init_dynamic" && function.span.is_some()));

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
fn compiler_injected_freestanding_initializer_replaces_the_redundant_hir_synthetic_body() {
    let source = "fn make_value() -> i64:\n    return 23\nval runtime_value: i64 = make_value()\n";
    let mut ast = simple_parser::Parser::new(source).parse().expect("parse fixture");
    super::module_global_init::inject_freestanding_module_global_init(&mut ast, "os__shared");
    let mut lowerer = Lowerer::new();
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let mut hir = lowerer.lower_module(&ast).expect("lower freestanding fixture");
    assert!(hir
        .functions
        .iter()
        .any(|function| function.name == "__module_init_dynamic"));
    assert!(hir
        .functions
        .iter()
        .any(|function| function.name == "__module_init_os__shared_dynamic"));

    assign_native_dynamic_initializer_identity(&mut hir, "os__shared").unwrap();

    assert!(!hir
        .functions
        .iter()
        .any(|function| function.name == "__module_init_dynamic"));
    assert_eq!(
        hir.functions
            .iter()
            .filter(|function| function.name == "__module_init_os__shared_dynamic")
            .count(),
        1
    );
}

#[cfg(not(target_os = "windows"))]
#[test]
fn two_same_basename_modules_link_and_run_both_runtime_global_initializers() {
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
    let left_source = "fn make_value() -> i64:\n    return 11\nval runtime_value: i64 = make_value()\nfn read_value() -> i64:\n    return runtime_value\n";
    let right_source = "fn make_value() -> i64:\n    return 31\nval runtime_value: i64 = make_value()\nfn read_value() -> i64:\n    return runtime_value\n";
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
            "#include <stdint.h>\nextern void __simple_call_module_inits(void);\nextern int64_t {left_prefix}__read_value(void);\nextern int64_t {right_prefix}__read_value(void);\nint main(void) {{ __simple_call_module_inits(); return ({left_prefix}__read_value() == 11 && {right_prefix}__read_value() == 31) ? 0 : 1; }}\n",
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
        "runtime initializers did not produce both values: status={:?} stderr={}",
        run.status.code(),
        String::from_utf8_lossy(&run.stderr)
    );
}
