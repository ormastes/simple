//! Follow-ups to `imported_fn_value_native.rs` (PR #3998). Each entry in
//! `test/fixtures/native/fn_value_followups` must native-build and print its
//! PASS line on both backends:
//! - `option_untyped.spl`: an UNTYPED `val m = Some(f)` (local and imported).
//!   Pre-fix LLVM answered a wrong result.
//! - `global_fn.spl`: a module-level `val F = some_fn`. Pre-fix cranelift
//!   stored a direct record that `rt_closure_func_ptr` rejects (call to 0).
//! - `pool_fn.spl`: a function value submitted to the runtime pool. Pre-fix
//!   the pool accepted only direct records, so cranelift's closure values
//!   were rejected.
//! See doc/08_tracking/bug/native_imported_fn_value_null_call_2026-10-20.md.

use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use std::path::PathBuf;

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

static ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn build_and_run(backend: &str, entry: &str, expected: &str) {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let source = repo.join("test/fixtures/native/fn_value_followups");
    let temporary = tempfile::tempdir().unwrap();
    let executable = temporary.path().join(if cfg!(windows) { "probe.exe" } else { "probe" });
    let _environment = BootstrapEnvironment::enter();
    let result = NativeProjectBuilder::new(repo, executable.clone())
        .config(NativeBuildConfig {
            backend: backend.to_string(),
            runtime_bundle: "core-c-bootstrap".to_string(),
            entry_closure: true,
            parallel: false,
            num_threads: Some(1),
            cache_dir: Some(temporary.path().join("native-cache")),
            ..NativeBuildConfig::default()
        })
        .source_dir(source.clone())
        .entry_file(source.join(entry))
        .build()
        .unwrap_or_else(|e| panic!("{backend} {entry}: native build must succeed: {e:?}"));
    assert_eq!(result.failed, 0, "{backend} {entry}: failed units");
    let run = std::process::Command::new(executable).output().unwrap();
    assert!(
        run.status.success(),
        "{backend} {entry}: status={} stdout={} stderr={}",
        run.status,
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), expected, "{backend} {entry}");
}

#[test]
fn option_untyped_fn_value_cranelift() {
    build_and_run("cranelift", "option_untyped.spl", "option-untyped PASS");
}

#[cfg(feature = "llvm")]
#[test]
fn option_untyped_fn_value_llvm() {
    build_and_run("llvm", "option_untyped.spl", "option-untyped PASS");
}

#[test]
fn global_fn_value_cranelift() {
    build_and_run("cranelift", "global_fn.spl", "global-fn PASS");
}

#[cfg(feature = "llvm")]
#[test]
fn global_fn_value_llvm() {
    build_and_run("llvm", "global_fn.spl", "global-fn PASS");
}

#[test]
fn pool_fn_value_cranelift() {
    build_and_run("cranelift", "pool_fn.spl", "pool-fn PASS");
}

#[cfg(feature = "llvm")]
#[test]
fn pool_fn_value_llvm() {
    build_and_run("llvm", "pool_fn.spl", "pool-fn PASS");
}
