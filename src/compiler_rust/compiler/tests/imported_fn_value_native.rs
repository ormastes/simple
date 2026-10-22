//! A function defined in ANOTHER compilation unit, taken as a VALUE (variable,
//! struct field, Option payload, callback argument), must call the real body
//! after a native build. Pre-fix the cranelift GlobalLoad lowered an imported
//! name to a bare `rt_alloc` "direct record" that `rt_closure_func_ptr`
//! rejects, so the indirect call jumped to address 0.
//! See doc/08_tracking/bug/native_imported_fn_value_null_call_2026-10-20.md.

use std::path::PathBuf;
use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};

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

fn build_and_run(backend: &str) {
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let source = repo.join("test/fixtures/native/imported_fn_value");
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
        .entry_file(source.join("main.spl"))
        .build()
        .unwrap_or_else(|e| panic!("{backend}: native build must succeed: {e:?}"));
    assert_eq!(result.failed, 0, "{backend}: failed units");
    let run = std::process::Command::new(executable).output().unwrap();
    assert!(
        run.status.success(),
        "{backend}: status={} stdout={} stderr={}",
        run.status,
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "imported-fn-value PASS", "{backend}");
}

#[test]
fn imported_fn_value_cranelift() {
    build_and_run("cranelift");
}

#[cfg(feature = "llvm")]
#[test]
fn imported_fn_value_llvm() {
    build_and_run("llvm");
}
