//! Exercise integer text dispatch through an actual LLVM/core-C native
//! executable while the real SDN enum method is in the same linked closure.
#![cfg(feature = "llvm")]

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

#[test]
fn integer_to_text_dispatch_keeps_width_alias_and_sdn_semantics_on_llvm_core_c() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let temporary = tempfile::tempdir().unwrap();
    let source = temporary.path().join("src");
    std::fs::create_dir_all(&source).unwrap();
    std::fs::copy(
        repo.join("test/fixtures/native/integer_to_text_dispatch/main.spl"),
        source.join("main.spl"),
    )
    .unwrap();
    let executable = temporary.path().join("integer_to_text_dispatch_probe");
    let _environment = BootstrapEnvironment::enter();
    let result = NativeProjectBuilder::new(repo.clone(), executable.clone())
        .config(NativeBuildConfig {
            backend: "llvm".to_string(),
            runtime_bundle: "core-c-bootstrap".to_string(),
            entry_closure: true,
            parallel: true,
            num_threads: Some(10),
            cache_dir: Some(temporary.path().join("native-cache")),
            ..NativeBuildConfig::default()
        })
        .source_dir(repo.join("src/lib"))
        .source_dir(repo.join("src/app"))
        .source_dir(source.clone())
        .entry_file(source.join("main.spl"))
        .build()
        .expect("native LLVM/core-C integer text-dispatch build must succeed");
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
        "PASS primitive-text-width-alias-frame-and-sdn"
    );
}
