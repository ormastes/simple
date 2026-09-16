# SCV wasm availability probe crashed (E-SFFI-001) when build/libspl_wasmtime.so is absent (2026-08-26, FIXED)

**Found by:** W4 + Wave-1 closeout lane. `scv_incremental_parse_spec.spl` went
9/9 -> 2/9 mid-session with
`runtime: E-SFFI-001: spl_dlopen failed for 'build/libspl_wasmtime.so'`.

**Root cause:** `scv_wasm_executor_available()` (src/lib/scv/wasm_executor.spl)
probes with `DynLib.load(path)`, whose contract assumes `spl_dlopen` returns
<=0 on failure. On this interpreter, `spl_dlopen` of a MISSING file instead
raises a hard E-SFFI-001 runtime error, so the "graceful fallback" probe dies
before it can answer false. The probe only appeared to work while a stray
`build/libspl_wasmtime.so` happened to exist (built by an earlier lane on the
shared box); when the shared `build/` churned it away, every caller crashed.
A probe that only answers correctly when the answer is "yes" is fail-open.

**Fix:** existence pre-check (`file_exists`) on both `sffi_lib_path("wasmtime")`
and `sffi_lib_path("scv_wasm")` before any `DynLib.load` in the probe.
Reproduce: `bin/simple test test/integration/app/scv_incremental_parse_spec.spl`
with no `build/libspl_wasmtime.so` — 2/9 pre-fix, 9/9 post-fix (fallback mode,
honestly reported as `fallback-full-reparse`).

**Class note / remaining:** the deeper defect is the `spl_dlopen` contract
mismatch (raise vs return <=0) in the runtime; any other `DynLib.load` on a
possibly-missing path is the same class. `src/lib/scv` callers were swept —
`wasm_executor.spl` was the only unguarded probe. The runtime-side contract
fix is filed here as follow-up, not silently normalized.
