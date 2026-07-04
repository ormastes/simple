//! Regression test for task #97: native-build must not silently fabricate a
//! zero-returning stub for a genuine `rt_*` runtime ABI symbol that the
//! runtime library does not actually define. Before this guard, a
//! misspelled/missing `extern fn rt_*` declaration would link clean (thanks
//! to the bootstrap auto-stub generator + `--unresolved-symbols=ignore-all`)
//! and only crash the first time it was actually called — exactly the
//! failure mode that burned rt_get_host_target_code and rt_value_print (#93).
//!
//! This test bypasses the full Simple compiler pipeline (parser/HIR/MIR) and
//! instead compiles tiny hand-written C stand-ins for "an object file that
//! references an rt_* symbol", then drives `NativeBinaryBuilder` directly —
//! the exact Rust struct patched for #97 — to keep the test fast and focused
//! on the linker guard itself.

use std::path::{Path, PathBuf};
use std::sync::Mutex;

use simple_common::target::Target;
use simple_compiler::linker::NativeBinaryBuilder;

/// `NativeBinaryBuilder::build()` reads process-global env vars
/// (`SIMPLE_BOOTSTRAP`, `SIMPLE_ALLOW_UNRESOLVED_RT`, `SIMPLE_RUNTIME_PATH`);
/// serialize the two scenarios in this file so they can't race each other or
/// any other integration test binary running in the same process... note:
/// integration tests in `tests/*.rs` each get their own process, so this only
/// guards the two sub-scenarios within this file.
static ENV_GUARD: Mutex<()> = Mutex::new(());

fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler_rust dir")
        .to_path_buf()
}

/// Locate a directory containing a real `libsimple_runtime.a`, built by an
/// earlier `cargo build` of the workspace. Returns `None` (test is skipped,
/// not failed) if no runtime archive is available in this checkout — the
/// guard is designed to fail *open* (skip) when it can't inspect the runtime,
/// so without a real archive there is nothing meaningful to assert.
fn find_real_runtime_dir() -> Option<PathBuf> {
    let root = workspace_root();
    let candidates = [
        std::env::var("SIMPLE_RUNTIME_PATH").ok().map(PathBuf::from),
        Some(root.join("target/bootstrap/deps")),
        Some(root.join("target/bootstrap")),
        Some(root.join("target/debug/deps")),
        Some(root.join("target/debug")),
        Some(root.join("target/release/deps")),
        Some(root.join("target/release")),
    ];
    candidates
        .into_iter()
        .flatten()
        .find(|dir| dir.join("libsimple_runtime.a").exists())
}

fn cc() -> String {
    std::env::var("CC").unwrap_or_else(|_| {
        if std::process::Command::new("clang").arg("--version").output().is_ok() {
            "clang".to_string()
        } else {
            "gcc".to_string()
        }
    })
}

/// Compile a tiny C source defining `spl_main()` that calls `extern` symbol
/// `rt_symbol` into an object file, returning the raw object bytes.
fn compile_stub_object(rt_symbol: &str, out_dir: &Path) -> Vec<u8> {
    let c_path = out_dir.join(format!("{rt_symbol}.c"));
    let o_path = out_dir.join(format!("{rt_symbol}.o"));
    std::fs::write(
        &c_path,
        format!(
            r#"
#include <stdint.h>
extern int64_t {sym}(void);
int spl_main(void) {{
    return (int){sym}();
}}
"#,
            sym = rt_symbol
        ),
    )
    .expect("write stub c source");
    let status = std::process::Command::new(cc())
        .arg("-c")
        .arg("-o")
        .arg(&o_path)
        .arg(&c_path)
        .status()
        .expect("invoke cc");
    assert!(status.success(), "failed to compile stub object for {rt_symbol}");
    std::fs::read(&o_path).expect("read stub object")
}

#[test]
fn rejects_missing_rt_extern_but_allows_real_ones() {
    let Some(runtime_dir) = find_real_runtime_dir() else {
        eprintln!("SKIP: no libsimple_runtime.a found in this checkout; nothing to guard against");
        return;
    };
    eprintln!("Using runtime dir: {}", runtime_dir.display());

    let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
    let temp_dir = tempfile::tempdir().expect("tempdir");

    // SAFETY: serialized by ENV_GUARD; no other thread in this test binary
    // touches these vars while held.
    unsafe {
        std::env::set_var("SIMPLE_BOOTSTRAP", "1");
        std::env::set_var("SIMPLE_RUNTIME_PATH", &runtime_dir);
        std::env::remove_var("SIMPLE_ALLOW_UNRESOLVED_RT");
    }

    // --- Case 1: undeclared/missing rt_* extern must FAIL the build, naming the symbol.
    {
        let obj = compile_stub_object("rt_definitely_missing_xyz", temp_dir.path());
        let out_path = temp_dir.path().join("missing_out");
        let result = NativeBinaryBuilder::new(obj)
            .target(Target::host())
            .output(&out_path)
            .build();

        assert!(
            result.is_err(),
            "expected build() to reject an undeclared rt_* extern, but it succeeded"
        );
        let message = format!("{}", result.unwrap_err());
        assert!(
            message.contains("rt_definitely_missing_xyz"),
            "error message should name the offending symbol, got: {message}"
        );
    }

    // --- Case 2: a real, runtime-provided rt_* symbol must still link fine.
    {
        // rt_getpid is defined by libsimple_runtime.a (see stubs.rs RT_KEEP);
        // this proves the guard doesn't false-positive on legitimate externs.
        let obj = compile_stub_object("rt_getpid", temp_dir.path());
        let out_path = temp_dir.path().join("real_out");
        let result = NativeBinaryBuilder::new(obj)
            .target(Target::host())
            .output(&out_path)
            .build();

        assert!(
            result.is_ok(),
            "expected build() to succeed for a real runtime rt_* extern, got: {:?}",
            result.err()
        );
    }

    // --- Case 3: escape hatch — SIMPLE_ALLOW_UNRESOLVED_RT=1 downgrades to a warning.
    {
        unsafe {
            std::env::set_var("SIMPLE_ALLOW_UNRESOLVED_RT", "1");
        }
        let obj = compile_stub_object("rt_definitely_missing_xyz", temp_dir.path());
        let out_path = temp_dir.path().join("escape_hatch_out");
        let result = NativeBinaryBuilder::new(obj)
            .target(Target::host())
            .output(&out_path)
            .build();
        unsafe {
            std::env::remove_var("SIMPLE_ALLOW_UNRESOLVED_RT");
        }

        assert!(
            result.is_ok(),
            "expected SIMPLE_ALLOW_UNRESOLVED_RT=1 to bypass the guard, got: {:?}",
            result.err()
        );
    }

    unsafe {
        std::env::remove_var("SIMPLE_BOOTSTRAP");
        std::env::remove_var("SIMPLE_RUNTIME_PATH");
    }
}
