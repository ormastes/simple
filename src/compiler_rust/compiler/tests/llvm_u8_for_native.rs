//! Exercise the LLVM/core-C boundary that Cranelift-only iteration tests miss:
//! C rt_array_get returns packed bytes raw, while Rust's getter boxes them.
//! This is an explicit bootstrap compiler diagnostic, not a tooling fallback.
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
fn u8_for_preserves_packed_slots_and_published_bytes_on_llvm_core_c() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let temporary = tempfile::tempdir().unwrap();
    let source = temporary.path().join("src");
    std::fs::create_dir_all(&source).unwrap();
    std::fs::copy(
        repo.join("test/fixtures/native/u8_for_iteration/main.spl"),
        source.join("main.spl"),
    )
    .unwrap();
    let executable = temporary.path().join("u8_for_probe");
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
        .expect("native LLVM/core-C build must succeed");
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
        "PASS packed-slot-copies-publication"
    );
    // Independently pinned SHA-256, not a digest recomputed through Simple's
    // same conversion path. Read raw disk bytes without a text codec.
    let manifest = temporary
        .path()
        .join("receipts/manifests/26ef0588f5b072964404b2ce5320d6014703180854759e5b53ddae06621beb6c.manifest");
    assert_eq!(
        std::fs::read(manifest).unwrap(),
        b"simple-target-dependency-manifest-v1\nconsumer=h08px-native-byte-copy\n"
    );
}
