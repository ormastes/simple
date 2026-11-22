//! LLVM float `%`: the seed rejected it with `Unsupported float binop: Mod`,
//! so `src/runtime/simple_core/core_any_ops.spl` (and the simple-core archive)
//! could not be built. The fixture checks floored semantics for f64 and f32
//! with both operand signs, matching the interpreter and the cranelift backend.
//! See doc/08_tracking/bug/seed_llvm_float_mod_unsupported_blocks_simple_core_archive_2026-11-22.md
#![cfg(feature = "llvm")]

use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use std::path::PathBuf;

// This integration target contains one test and owns its process environment.
struct BootstrapEnvironment(Vec<(&'static str, Option<std::ffi::OsString>)>);

impl BootstrapEnvironment {
    fn enter() -> Self {
        let previous = ["SIMPLE_BOOTSTRAP", "SIMPLE_NO_STUB_FALLBACK"]
            .into_iter()
            .map(|name| {
                let value = std::env::var_os(name);
                std::env::set_var(name, "1");
                (name, value)
            })
            .collect();
        Self(previous)
    }
}

impl Drop for BootstrapEnvironment {
    fn drop(&mut self) {
        for (name, previous) in &self.0 {
            match previous {
                Some(value) => std::env::set_var(name, value),
                None => std::env::remove_var(name),
            }
        }
    }
}

#[test]
fn float_mod_is_floored_for_f64_and_f32_on_llvm_core_c() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let temporary = tempfile::tempdir().unwrap();
    let source = temporary.path().join("src");
    std::fs::create_dir_all(&source).unwrap();
    std::fs::copy(
        repo.join("test/fixtures/native/f64_mod/main.spl"),
        source.join("main.spl"),
    )
    .unwrap();
    let executable = temporary.path().join("f64_mod_probe");
    let _environment = BootstrapEnvironment::enter();
    let result = NativeProjectBuilder::new(repo.clone(), executable.clone())
        .config(NativeBuildConfig {
            backend: "llvm".to_string(),
            runtime_bundle: "core-c-bootstrap".to_string(),
            entry_closure: true,
            cache_dir: Some(temporary.path().join("native-cache")),
            ..NativeBuildConfig::default()
        })
        .source_dir(source.clone())
        .entry_file(source.join("main.spl"))
        .build()
        .expect("native LLVM/core-C build with float % must succeed");
    assert_eq!(result.failed, 0);
    let run = std::process::Command::new(executable)
        .current_dir(temporary.path())
        .output()
        .unwrap();
    assert!(
        run.status.success(),
        "status={} stdout={} stderr={}",
        run.status,
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&run.stdout).trim(),
        "PASS float-mod-floored-semantics"
    );
}
