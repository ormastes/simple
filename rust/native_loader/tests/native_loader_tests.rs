use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::Arc;

use simple_native_loader::{ModuleLoader, ModuleRegistry};

fn build_temp_so(source: &str, name: &str) -> (tempfile::TempDir, PathBuf) {
    let dir = tempfile::tempdir().unwrap();
    let c_path = dir.path().join(format!("{name}.c"));
    let so_path = dir.path().join(format!("lib{name}.so"));
    fs::write(&c_path, source).unwrap();

    let status = Command::new("cc")
        .args([
            "-shared",
            "-fPIC",
            c_path.to_str().unwrap(),
            "-o",
            so_path.to_str().unwrap(),
        ])
        .status()
        .expect("failed to invoke cc");
    assert!(status.success(), "cc failed");

    (dir, so_path)
}

#[test]
fn loader_loads_native_function() {
    let (_dir, so_path) = build_temp_so(
        r#"
        long add(long a, long b) { return a + b; }
        "#,
        "addlib",
    );

    let loader = ModuleLoader::new();
    let module = loader.load(&so_path).expect("should load library");

    type AddFn = unsafe extern "C" fn(i64, i64) -> i64;
    let add: AddFn = module.get_function("add").expect("symbol should resolve");
    let result = unsafe { add(2, 3) };
    assert_eq!(result, 5);
}

#[test]
fn registry_caches_native_module() {
    let (_dir, so_path) = build_temp_so(
        r#"
        int main() { return 42; }
        "#,
        "mainlib",
    );

    let registry = ModuleRegistry::default();
    let first = registry.load(&so_path).expect("load ok");
    let second = registry.load(&so_path).expect("load cached");
    assert!(Arc::ptr_eq(&first, &second));

    type MainFn = unsafe extern "C" fn() -> i32;
    let entry: MainFn = first.entry_point().expect("main symbol");
    let value = unsafe { entry() };
    assert_eq!(value, 42);
}

#[test]
fn registry_unload_removes_module() {
    let (_dir, so_path) = build_temp_so(
        r#"
        int val() { return 1; }
        "#,
        "unloadlib",
    );

    let registry = ModuleRegistry::default();
    let _first = registry.load(&so_path).expect("load ok");

    // Unload should return true (module was cached)
    assert!(registry.unload(&so_path));

    // Unload again should return false (nothing to remove)
    assert!(!registry.unload(&so_path));
}

#[test]
fn registry_reload_replaces_cached_module() {
    let (_dir, so_path) = build_temp_so(
        r#"
        int version() { return 1; }
        "#,
        "reloadlib",
    );

    let registry = ModuleRegistry::default();
    let first = registry.load(&so_path).expect("load ok");
    let first_ptr = Arc::as_ptr(&first);

    // Reload creates a new module instance
    let reloaded = registry.reload(&so_path).expect("reload ok");
    let reloaded_ptr = Arc::as_ptr(&reloaded);

    // The pointers should be different (new module loaded)
    assert_ne!(first_ptr, reloaded_ptr);

    // Getting the module again should return the reloaded version
    let cached = registry.load(&so_path).expect("load from cache");
    assert!(Arc::ptr_eq(&reloaded, &cached));
}

#[test]
fn registry_load_nonexistent_fails() {
    let registry = ModuleRegistry::default();
    let result = registry.load(std::path::Path::new("/nonexistent/path/lib.so"));
    assert!(result.is_err());
}

#[test]
fn registry_unload_nonexistent_returns_false() {
    let registry = ModuleRegistry::default();
    let result = registry.unload(std::path::Path::new("/nonexistent/path/lib.so"));
    assert!(!result);
}

#[test]
fn loader_get_function_nonexistent_returns_none() {
    let (_dir, so_path) = build_temp_so(
        r#"
        int exists() { return 42; }
        "#,
        "fnchecklib",
    );

    let loader = ModuleLoader::new();
    let module = loader.load(&so_path).expect("should load");

    type SomeFn = unsafe extern "C" fn() -> i32;
    let missing: Option<SomeFn> = module.get_function("nonexistent_function");
    assert!(missing.is_none());

    let existing: Option<SomeFn> = module.get_function("exists");
    assert!(existing.is_some());
}

#[test]
fn module_entry_point_returns_none_without_main() {
    let (_dir, so_path) = build_temp_so(
        r#"
        int not_main() { return 99; }
        "#,
        "nomainlib",
    );

    let loader = ModuleLoader::new();
    let module = loader.load(&so_path).expect("should load");

    // No 'main' symbol, so entry_point should return None
    type MainFn = unsafe extern "C" fn() -> i32;
    let entry: Option<MainFn> = module.entry_point();
    assert!(entry.is_none());

    // But named function should work
    let func: Option<MainFn> = module.get_function("not_main");
    assert!(func.is_some());
    let result = unsafe { func.unwrap()() };
    assert_eq!(result, 99);
}

#[test]
fn module_dyn_module_trait_works() {
    use simple_common::DynModule;

    let (_dir, so_path) = build_temp_so(
        r#"
        int main() { return 77; }
        int helper() { return 11; }
        "#,
        "dynmodlib",
    );

    let loader = ModuleLoader::new();
    let module = loader.load(&so_path).expect("should load");

    // Test via trait
    type IntFn = unsafe extern "C" fn() -> i32;

    let entry: Option<IntFn> = DynModule::entry_fn(&module);
    assert!(entry.is_some());
    assert_eq!(unsafe { entry.unwrap()() }, 77);

    let helper: Option<IntFn> = DynModule::get_fn(&module, "helper");
    assert!(helper.is_some());
    assert_eq!(unsafe { helper.unwrap()() }, 11);

    let missing: Option<IntFn> = DynModule::get_fn(&module, "missing");
    assert!(missing.is_none());
}

#[test]
fn module_version_is_set() {
    let (_dir, so_path) = build_temp_so(
        r#"
        int foo() { return 1; }
        "#,
        "versionlib",
    );

    let loader = ModuleLoader::new();
    let module = loader.load(&so_path).expect("should load");

    // Version should be initialized
    assert_eq!(module.version, 1);
}

#[test]
fn module_path_is_set() {
    let (_dir, so_path) = build_temp_so(
        r#"
        int bar() { return 2; }
        "#,
        "pathlib",
    );

    let loader = ModuleLoader::new();
    let module = loader.load(&so_path).expect("should load");

    // Path should match what we loaded
    assert_eq!(module.path.canonicalize().ok(), so_path.canonicalize().ok());
}
