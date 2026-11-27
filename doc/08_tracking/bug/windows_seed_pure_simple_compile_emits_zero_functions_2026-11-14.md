# Windows: pure-Simple `compile --native` run under the seed emits ZERO functions for any module (both backends)

Date: 2026-11-14
Status: verification-pending (fixed by PR #9153; re-verified 2026-11-14 by lane xrayfg: llvm backend, 3 functions exported)
Related: `xray_llvm_simple_compiled_module_emits_zero_functions_2026-11-13.md` (Linux/aarch64, same
symptom), `native_backend_no_win64_target_coff_emitter_2026-11-14.md`.

## Result of the step-0 probe
Not XRay-specific and not LLVM-specific. On this Windows host, with the seed-tip seed
(`/c/dev/wt/seed-tip/simple.exe`) running the pure-Simple CLI entry (driver copied from
`test/fixtures/xray/xray_native_cli_compile_driver.spl`, entry `cli_compile_pure_simple`,
`SIMPLE_NATIVE_BUILD_EMIT_OBJECT=shared`, llvm-mingw UCRT clang as `CC`, no `--xray`):

| module | backend | outcome |
|---|---|---|
| `test/fixtures/xray/xray_inprocess_prog.spl` | `native` | rc=0, DLL links, but the only export is `simple_empty_module_test_fixtures_xray_xray_inprocess_prog`; lane receipt `functions_emitted=0 statics_emitted=0` |
| same, plus `pub fn` on every fn and a `fn main()` | `native` | same receipt, `functions_emitted=0` |
| same | `llvm` (pure-Simple lane) | `functions_emitted=0`; then link fails: `error: shared-library link failed: Windows GNU shared linking requires bootstrap-owned clang through CC` (passes once `CC` is set; the zero-function object is the same) |
| same, via `cli_compile(["compile","--native","--backend=llvm",...])` | llvm | `error: native backend 'llvm' is not available in this build; rebuild with --features llvm` (seed built without the llvm feature; that route goes to the Rust seed) |

Receipt line (identical in all three non-error rows):

    [WARN] non-vacuity: lane_receipt name=native-build verdict=mismatch modules_seen=1
      modules_lowered=1 modules_objectless=0 functions_emitted=0 statics_emitted=0 objects_written=1
      link_inputs=1 reason=emitted zero functions and zero statics

`driver_aot_native_output.spl:~4405` then emits the empty translation unit
(`mir_module.functions.keys().len() == 0`), so the MIR module reaching codegen is empty: HIR phase
reports `done=1`, MIR phase `lower_to_mir` starts, and no function survives. Wall time ~80 s per run.

## Consequence
No pure-Simple Windows DLL with real functions can be produced on this host today, so the
flag-guard IR-sled design (LLVM translator) has nothing to instrument and no host can dlopen and
call a Simple function. IR-text emission (translator unit specs) is still testable, but the
real run (step 4) and overhead numbers are blocked until a module with functions is produced.

## Repro
    cd <worktree>; export CC=<llvm-mingw>/bin/clang.exe PATH=<llvm-mingw>/bin:$PATH
    XR_SRC=test/fixtures/xray/xray_inprocess_prog.spl XR_OUT=out.dll XR_XRAY=0 \
      SIMPLE_NATIVE_BUILD_EMIT_OBJECT=shared /c/dev/wt/seed-tip/simple.exe run <driver>.spl

## Next
Root-cause where `lower_to_mir` drops all functions under the Windows seed (compare with the same
fixture on Linux where `--backend=native` yields functions); add a repro spec asserting
`functions_emitted > 0` for a two-function library module.
