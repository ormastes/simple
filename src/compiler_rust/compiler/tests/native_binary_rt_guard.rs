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

/// Compile an object that contains a WEAK, ZERO-SIZE definition of `symbol` —
/// byte-for-byte the shape that Simple codegen emits for an `@extern fn` with no
/// implementation anywhere (measured on 2026-08-01: `nm -S main.o` reports
/// `0000000000000000 W <name>`, i.e. weak, defined, no size, empty body).
///
/// Because the symbol is *defined*, it never shows up in `nm -u`, which is why the
/// `nm -u`-based #97 guard could not see it and the build linked clean.
fn compile_fabricated_extern_object(symbol: &str, out_dir: &Path) -> Vec<u8> {
    let c_path = out_dir.join(format!("fab_{symbol}.c"));
    let o_path = out_dir.join(format!("fab_{symbol}.o"));
    std::fs::write(
        &c_path,
        format!(
            r#"
#include <stdint.h>
__asm__(".weak {sym}\n{sym}:\n");
extern int64_t {sym}(void);
int spl_main(void) {{
    return (int){sym}();
}}
"#,
            sym = symbol
        ),
    )
    .expect("write fabricated-extern c source");
    let status = std::process::Command::new(cc())
        .arg("-c")
        .arg("-o")
        .arg(&o_path)
        .arg(&c_path)
        .status()
        .expect("invoke cc");
    assert!(
        status.success(),
        "failed to compile fabricated-extern object for {symbol}"
    );
    std::fs::read(&o_path).expect("read fabricated-extern object")
}

/// Regression test for the native-lane member of the "unregistered extern silently
/// returns 0" family (2026-08-01).
///
/// RED before the fix: `NativeBinaryBuilder::build()` linked this object clean and
/// produced a runnable binary, because the fabricated symbol is DEFINED (weak,
/// zero-size) and therefore invisible to the `nm -u`-based #97 guard. Reproduced
/// end-to-end through `simple compile --native` with `@extern fn
/// lane_definitely_absent(x: i64) -> i64` and no implementation: build exit 0,
/// artifact produced, guard silent — for BOTH an `rt_`-prefixed and a non-`rt_`
/// symbol name, with and without `SIMPLE_BOOTSTRAP=1`.
///
/// Note the prefix is irrelevant here on purpose: case 1 uses a non-`rt_` name (the
/// class the old guard filtered out entirely) and case 2 uses an `rt_` name (which
/// the old guard *claimed* to cover but structurally could not).
#[test]
fn rejects_fabricated_weak_empty_extern_definitions() {
    let _guard = ENV_GUARD.lock().unwrap_or_else(|e| e.into_inner());
    let temp_dir = tempfile::tempdir().expect("tempdir");

    // --- Case 1: non-`rt_` fabricated extern must FAIL the build, naming the symbol.
    {
        let obj = compile_fabricated_extern_object("lane_definitely_absent", temp_dir.path());
        let out_path = temp_dir.path().join("fab_nonrt_out");
        let result = NativeBinaryBuilder::new(obj)
            .target(Target::host())
            .output(&out_path)
            .build();

        assert!(
            result.is_err(),
            "expected build() to reject a fabricated weak/empty non-rt_ extern, but it succeeded"
        );
        let message = format!("{}", result.unwrap_err());
        assert!(
            message.contains("lane_definitely_absent"),
            "error message should name the offending symbol, got: {message}"
        );
    }

    // --- Case 2: same defect with an `rt_` name — the old guard could not see this either.
    {
        let obj = compile_fabricated_extern_object("rt_lane_definitely_absent", temp_dir.path());
        let out_path = temp_dir.path().join("fab_rt_out");
        let result = NativeBinaryBuilder::new(obj)
            .target(Target::host())
            .output(&out_path)
            .build();

        assert!(
            result.is_err(),
            "expected build() to reject a fabricated weak/empty rt_ extern, but it succeeded"
        );
        let message = format!("{}", result.unwrap_err());
        assert!(
            message.contains("rt_lane_definitely_absent"),
            "error message should name the offending symbol, got: {message}"
        );
    }

    // --- Case 3: NON-VACUITY CONTROL. An object with no fabricated symbols must still
    // build. Without this, cases 1 and 2 would also pass if build() always failed.
    // Measured on a real program (structs, generics, List, string interpolation,
    // `print`): zero weak zero-size definitions, so the guard does not false-positive.
    {
        let c_path = temp_dir.path().join("control.c");
        let o_path = temp_dir.path().join("control.o");
        std::fs::write(&c_path, "int spl_main(void) { return 7; }\n").expect("write control c");
        let status = std::process::Command::new(cc())
            .arg("-c")
            .arg("-o")
            .arg(&o_path)
            .arg(&c_path)
            .status()
            .expect("invoke cc");
        assert!(status.success(), "failed to compile control object");
        let obj = std::fs::read(&o_path).expect("read control object");

        let out_path = temp_dir.path().join("control_out");
        let result = NativeBinaryBuilder::new(obj)
            .target(Target::host())
            .output(&out_path)
            .build();

        assert!(
            result.is_ok(),
            "control object with no fabricated symbols must still link, got: {:?}",
            result.err()
        );
    }
}
