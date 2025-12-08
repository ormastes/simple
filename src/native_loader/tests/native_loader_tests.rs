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

    let registry = ModuleRegistry::new();
    let first = registry.load(&so_path).expect("load ok");
    let second = registry.load(&so_path).expect("load cached");
    assert!(Arc::ptr_eq(&first, &second));

    type MainFn = unsafe extern "C" fn() -> i32;
    let entry: MainFn = first.entry_point().expect("main symbol");
    let value = unsafe { entry() };
    assert_eq!(value, 42);
}
