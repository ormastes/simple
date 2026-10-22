//! LLVM typed-bytes little-endian reads, as a real native executable: pinned
//! values for bytes 01..08 (u32 at 0 = 0x04030201, u64 at 0 =
//! 0x0807060504030201) on a packed `[u8]` and on a slot-layout one (a `[]`
//! literal in a struct field). The in-process LLVM JIT cannot run array code
//! (any `[u8]` push segfaults there), hence the native build.
//! Bug: doc/08_tracking/bug/jit_hoisted_u8_data_ptr_ignores_slot_layout_2026-10-19.md
#![cfg(feature = "llvm")]

use simple_compiler::pipeline::{NativeBuildConfig, NativeProjectBuilder};
use std::path::PathBuf;

const SRC: &str = "extern fn rt_typed_bytes_u32_le_at(buf: [u8], off: u64) -> u64\nextern fn rt_typed_bytes_u64_le_at(buf: [u8], off: u64) -> u64\n\nstruct Holder:\n    bytes: [u8]\n\nfn fill(out: [u8]) -> [u8]:\n    var o = out\n    var i = 0\n    while i < 8:\n        o.push((i + 1).to_u8())\n        i = i + 1\n    o\n\nfn check(data: [u8]) -> i64:\n    var r = 0\n    if rt_typed_bytes_u32_le_at(data, 0u64) == 0x04030201u64:\n        r = r + 1\n    if rt_typed_bytes_u64_le_at(data, 0u64) == 0x0807060504030201u64:\n        r = r + 2\n    r\n\nfn main():\n    var packed: [u8] = []\n    print(\"le=\" + (check(fill(packed)) * 10 + check(fill(Holder(bytes: []).bytes))).to_text())\n";

/// Sets the bootstrap native-build env and restores it on drop (also on
/// panic). This target holds one test, so it runs in its own process and
/// cannot race other tests over the process environment.
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
fn le_word_reads_are_pinned_on_llvm_native() {
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let temporary = tempfile::tempdir().unwrap();
    let source = temporary.path().join("src");
    std::fs::create_dir_all(&source).unwrap();
    std::fs::write(source.join("main.spl"), SRC).unwrap();
    let executable = temporary.path().join("le_probe");
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
        .expect("native LLVM build must succeed");
    assert_eq!(result.failed, 0);
    let run = std::process::Command::new(executable).output().unwrap();
    assert!(run.status.success(), "status={} stderr={}", run.status, String::from_utf8_lossy(&run.stderr));
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "le=33");
}
