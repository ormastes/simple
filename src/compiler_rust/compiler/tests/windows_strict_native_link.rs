//! An actual MSVC unresolved link must fail without creating parity trap stubs.
#![cfg(all(feature = "llvm", target_os = "windows", target_env = "msvc"))]

use std::path::PathBuf;
use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};

#[test]
fn strict_windows_link_preserves_missing_symbol_error_without_stub_artifacts() {
    let previous = std::env::var_os("SIMPLE_NO_STUB_FALLBACK");
    std::env::set_var("SIMPLE_NO_STUB_FALLBACK", "1");
    let temporary = tempfile::tempdir().unwrap();
    let entry = temporary.path().join("main.spl");
    std::fs::write(&entry, "extern fn spl_strict_link_deliberately_missing() -> i64\nfn main() -> i64:\n    spl_strict_link_deliberately_missing()\n").unwrap();
    let executable = temporary.path().join("probe.exe");
    let cache = temporary.path().join("native-cache");
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let result = NativeProjectBuilder::new(repo, executable.clone())
        .config(NativeBuildConfig {
            backend: "llvm".to_string(),
            runtime_bundle: "core-c-bootstrap".to_string(),
            entry_closure: true,
            parallel: false,
            num_threads: Some(1),
            cache_dir: Some(cache.clone()),
            ..NativeBuildConfig::default()
        })
        .source_dir(temporary.path().to_path_buf())
        .entry_file(entry)
        .build();
    match previous {
        Some(value) => std::env::set_var("SIMPLE_NO_STUB_FALLBACK", value),
        None => std::env::remove_var("SIMPLE_NO_STUB_FALLBACK"),
    }
    let error = result.expect_err("a strict unresolved MSVC link cannot succeed with a trap stub");
    assert!(
        error.to_string().contains("spl_strict_link_deliberately_missing"),
        "{error}"
    );
    assert!(!executable.exists());
    assert!(!PathBuf::from(format!("{}.stubbed_symbols.txt", executable.display())).exists());
    let mut directories = vec![cache];
    while let Some(directory) = directories.pop() {
        if !directory.exists() {
            continue;
        }
        for item in std::fs::read_dir(directory).unwrap() {
            let path = item.unwrap().path();
            if path.is_dir() {
                directories.push(path);
            } else {
                assert!(
                    !matches!(
                        path.file_name().and_then(|name| name.to_str()),
                        Some("_gc_parity_stubs.c" | "_gc_parity_stubs.obj")
                    ),
                    "unexpected strict stub artifact {}",
                    path.display()
                );
            }
        }
    }
}
