//! Exercise imported optional array coalescing through the real native project
//! builder, then execute both the nil and present branches in both source forms.
#![cfg(feature = "llvm")]

use std::path::PathBuf;
use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};

struct BootstrapEnvironment(Vec<(&'static str, Option<std::ffi::OsString>)>);

impl BootstrapEnvironment {
    fn enter() -> Self {
        // This integration target has one test, in its own cargo test process.
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
fn imported_optional_array_coalesce_native_nil_and_present() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let source = repo.join("test/fixtures/native/optional_array_coalesce");
    let temporary = tempfile::tempdir().unwrap();
    let executable = temporary.path().join(if cfg!(windows) { "probe.exe" } else { "probe" });
    // Match the bootstrap native-build bridge while preserving caller state.
    let _environment = BootstrapEnvironment::enter();
    let result = NativeProjectBuilder::new(repo, executable.clone())
        .config(NativeBuildConfig {
            backend: "llvm".to_string(),
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
        .expect("actual imported optional-array native build must succeed");
    assert_eq!(result.failed, 0);
    let run = std::process::Command::new(executable).output().unwrap();
    assert!(
        run.status.success(),
        "status={} stdout={} stderr={}",
        run.status,
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&run.stdout).trim(),
        "optional-array-coalesce PASS"
    );
}
