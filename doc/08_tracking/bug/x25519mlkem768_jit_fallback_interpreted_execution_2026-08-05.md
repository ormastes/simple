# X25519MLKEM768: all hot-path operations run interpreted, not JIT-compiled

- **Date:** 2026-08-05
- **Severity:** P2 (perf — JIT lost on the entire hybrid-KEM hot path; program
  still runs correctly via interpreter fallback, so this is a benchmark
  attribution issue, not a correctness issue)
- **Campaign:** `x25519mlkem768_acceleration`, AC-9 performance report
- **Repro:** `bin/simple run <driver>` where `<driver>` calls any of
  `x25519_mlkem768_bench_keygen`, `_encapsulate`, `_decapsulate`, or `_kex`
  from `src/app/test/x25519mlkem768_perf_bench.spl` against
  `os.crypto.x25519_mlkem768.hybrid`.

## Details

Carried forward from an earlier investigation this session and corroborated
structurally here. Two distinct JIT-fallback blockers both sit on
`x25519_mlkem768_resolve_backend` (`src/os/crypto/x25519_mlkem768/execution_policy.spl:93`),
which every keygen/encapsulate/decapsulate call reaches:

1. **`cannot infer field type` on `X25519MlKem768Evidence.fallback_used`** —
   `fallback_used: bool` is declared at
   `src/lib/common/crypto/x25519_mlkem768/contract.spl:81` on
   `X25519MlKem768Evidence`, a struct imported across a module boundary by the
   resolver. This is the same defect class already tracked in
   `doc/08_tracking/bug/hir_lowering_bool_field_infer_imported_struct_2026-07-03.md`
   (HIR lowering cannot infer a `bool` field's type when the struct crosses a
   module boundary, e.g. `use ...contract.{X25519MlKem768Evidence}`), which
   drops the whole calling function to the interpreter.
2. **`unresolved external symbol 'cuda_module_load_binary'`** — costs a
   reported 16x when it fires, independent of (1).

Both are on the path called by every keygen, encapsulate, and decapsulate
operation, so the entire hybrid-KEM hot path measured for AC-9 runs
tree-walk-interpreted rather than JIT-compiled.

## Measured impact (AC-9 harness, n=17 repeats, rotated arm order, paired
   baseline subtraction, `/usr/bin/time -v` external wall clock, seed binary
   `bin/release/x86_64-unknown-linux-gnu/simple`)

| operation | median | range |
|---|---|---|
| keygen | 8042.4 ms | 6375.0 – 15661.7 ms |
| encapsulate | 8407.5 ms | 5450.6 – 13032.4 ms |
| decapsulate | 7942.7 ms | 4589.1 – 15542.8 ms |

Full numbers: `doc/09_report/x25519mlkem768_acceleration_performance_2026-08-05.md`.
Millisecond-scale interpreted overhead per call is consistent with tree-walk
dispatch through `resolve_backend`, not native/JIT execution of a ~constant-time
elliptic-curve/lattice operation (which would be sub-millisecond on this host).
By contrast `x25519_mlkem768_combine` (no `resolve_backend` call in its path)
measured 1.0 ms median — three orders of magnitude faster — which is
consistent with (but does not by itself prove) the same fallback pattern being
the dominant cost on the three slow arms.

## Expected

`X25519MlKem768Evidence.fallback_used` and other imported-struct `bool` fields
on the resolver's hot path should lower to HIR without an interpreter
fallback, once the general cross-module-`bool`-field HIR lowering gap
(`hir_lowering_bool_field_infer_imported_struct_2026-07-03.md`) is fixed. The
`cuda_module_load_binary` unresolved-symbol path needs a separate registration
fix. Both are compiler/runtime work, not X25519MLKEM768-specific, and are out
of scope for this benchmark pass per campaign instructions.

## Status

Not fixed in this pass (compiler-layer defect, explicitly out of scope for
the AC-9 measurement task). Recorded here so the AC-9 report's benchmark
numbers carry an accurate interpreted-execution attribution rather than being
read as native/JIT performance.
