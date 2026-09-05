//! Regression test: every freestanding boot path must call
//! `__simple_call_module_inits`.
//!
//! Heap-typed module globals (`var g: [T] = [...]`, `= "..."`, struct
//! literals) cannot live in `.data` — they are built at runtime by a
//! synthesized `__module_init_*` function, aggregated by the linker into
//! `__simple_call_module_inits` (`pipeline/native_project/linker.rs`
//! `generate_init_caller`).
//!
//! A HOSTED link gets that call for free from the generated `main` stub
//! (`linker.rs:802-806`). A FREESTANDING `--entry-closure` link has no such
//! stub: the ELF entry is the Simple entry function itself. The call must
//! therefore come from the target's own boot path, and nothing in the
//! compiler enforces that it does.
//!
//! Measured 2026-08-31 on `origin/main` @ `ea48917812b`: riscv64 had NO
//! caller anywhere — `arch/riscv64/boot/crt0.S` did not call it and neither
//! in-guest entry `.spl` declared it. Because nothing referenced the
//! aggregator, `--gc-sections` dropped it together with every
//! `__module_init_*`. The linked interpreter kernel
//! (`build/os/riscv64_interp/interp/kernel.elf`, seed-built,
//! `--target riscv64gc-unknown-none-elf --backend cranelift`) carried
//! **7167 symbols, zero `__module_init_*`, and no
//! `__simple_call_module_inits`**. Every module-level array global was a
//! null/zero handle in-guest — which is what left `core_last_token_text_slot`
//! (`src/compiler/10.frontend/core/lexer_struct.spl:60`) empty and stalled the
//! in-guest parser with `StringLit ''`.
//!
//! x86_64 was correct (`arch/x86_64/boot/crt0.s`, `.skip_module_inits`).
//! This test pins every freestanding boot path that reaches a Simple entry,
//! so the next architecture cannot silently ship without the call.

use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR = <repo>/src/compiler_rust/compiler
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(3)
        .expect("repo root above src/compiler_rust/compiler")
        .to_path_buf()
}

/// (human label, boot-path file relative to the repo root).
///
/// Each entry is the single place that architecture's freestanding boot
/// reaches a Simple entry point. Add a row when a new architecture gains an
/// in-guest lane — an architecture with no row is not "exempt", it is simply
/// not yet wired, and adding the lane without the row is the regression this
/// test exists to catch.
const FREESTANDING_BOOT_PATHS: &[(&str, &str)] = &[
    (
        "x86_64 example boot crt0",
        "examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s",
    ),
    (
        "riscv64 example boot shim",
        "examples/09_embedded/simple_os/arch/riscv64/boot/boot_entry.c",
    ),
];

#[test]
fn every_freestanding_boot_path_calls_simple_call_module_inits() {
    let root = repo_root();
    let mut checked = 0usize;
    let mut offenders = Vec::new();

    for (label, rel) in FREESTANDING_BOOT_PATHS {
        let path = root.join(rel);
        let source =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{label}: cannot read {}: {e}", path.display()));

        // Count only lines that CALL it, not the declaration and not prose.
        // C: `__simple_call_module_inits();`  asm: `call __simple_call_module_inits`
        let calls = source.lines().filter(|line| {
            let l = line.trim();
            if l.starts_with('*') || l.starts_with("//") || l.starts_with('#') {
                return false;
            }
            (l.contains("__simple_call_module_inits();") && !l.contains("void __simple_call_module_inits"))
                || l.starts_with("call __simple_call_module_inits")
                || l.starts_with("bl __simple_call_module_inits")
        });

        checked += 1;
        if calls.count() == 0 {
            offenders.push(format!("{label} ({rel})"));
        }
    }

    assert!(
        checked > 0,
        "ERROR — nothing was checked; FREESTANDING_BOOT_PATHS is empty"
    );
    assert!(
        offenders.is_empty(),
        "{checked} freestanding boot path(s) checked; {} never call \
         __simple_call_module_inits, so every heap-typed module global stays a \
         null handle in-guest: {}",
        offenders.len(),
        offenders.join(", ")
    );
}

/// Non-vacuity: the detector must actually reject a boot path that lacks the
/// call. Without this, a broken matcher would make the test above pass on
/// anything.
#[test]
fn detector_rejects_a_boot_path_without_the_call() {
    let without = "void boot_entry(void)\n{\n    spl_start();\n}\n";
    let with = "void boot_entry(void)\n{\n    __simple_call_module_inits();\n    spl_start();\n}\n";
    let has_call = |source: &str| {
        source.lines().any(|line| {
            let l = line.trim();
            !l.starts_with('*')
                && !l.starts_with("//")
                && l.contains("__simple_call_module_inits();")
                && !l.contains("void __simple_call_module_inits")
        })
    };
    assert!(!has_call(without), "detector must reject a boot path with no call");
    assert!(has_call(with), "detector must accept a boot path that calls it");
}
