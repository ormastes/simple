# BUG: interpreter — struct returned from imported module resolves as `Unit` in caller

- **ID:** `interp_cross_module_struct_return_unit`
- **Severity:** P1 (blocks cross-module struct-returning APIs in interpreter mode)
- **Found:** 2026-06-13, perf-umbrella Lane A (bench harness consumer test)
- **Family:** related to `native_cross_module_call_abi_broken_2026-05-18`,
  `jit_cross_module_extern_in_library_method_null_2026-06-13`,
  `hir_type_inference_any_field_2026-05-02` (cross-module type/ABI resolution cluster).

## Symptom
A struct constructed by a constructor function defined in module A (`make_bench_result`
in `src/app/test/bench/bench_harness.spl`) and returned to a caller in module B
(`test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl`) is seen by the caller as
`Unit` — field access / passing it to `bench_emit` fails. The value is correct when both
construction and use are in the same module.

## Repro
1. Module A: `fn make_bench_result(...) -> BenchResult: BenchResult{...}` with `export`.
2. Module B: `use A.*`; `val r = make_bench_result(...)`; access `r.value` → resolves Unit.
Run in interpreter mode (`bin/simple test <spec>`). The `bench_emit` file-existence case
is currently `pending()` because of this (label `interp_cross_module_struct_unit`).

## Impact
- Cross-module struct-returning stdlib/app APIs are unusable in interpreter mode.
- For the perf umbrella: benchmark specs must assert on primitives (mode strings, numeric
  results) rather than on returned `BenchResult` structs until fixed; doc emission via
  `bench_emit` works only in compiled mode.

## Suspected location (unverified)
Interpreter executor / type-metadata resolution. The pure-Simple interpreter lives at
`src/compiler/95.interp/`, but `bin/simple`'s default runtime path may delegate to the
Rust seed interpreter (`src/compiler_rust/`). **Locate the exact site before fixing** —
if it is in the Rust seed it is off-limits except via the seed-rebuild flow.

## Proposed next step (staged, P1 — "improve interpreter first")
1. Bisect: minimal 2-module struct-return repro under `test/fixtures/`.
2. Determine seed-interpreter vs pure-Simple `95.interp` ownership.
3. Fix in pure Simple if owned there; otherwise file a scoped seed change.
4. Add a regression spec; un-`pending()` the `bench_emit` consumer case.

## Status
OPEN — staged. Worked around in Lane A (assert on primitives). Not blocking P0 machinery.
