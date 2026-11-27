# Stage 2 Cranelift codegen keeps ~12 MiB per module: per-module scope was opt-in (2026-11-07)

- **ID:** stage2_cranelift_codegen_scope_default_off_2026-11-07
- **Priority:** P1 (last known bootstrap blocker: run 14 `compiler_cli_build` killed at the 60 GiB row cap)
- **Status:** fix-implemented
- **Related:** `native_codegen_unscoped_rss_growth_2026_10_24.md` (scope v2 placement, left opt-in),
  `codegen_module_memory_not_freed_per_module_2026_11_02.md` (LLVM object-path scope made default),
  `stage2_compiler_cli_build_mir_shard_share_unbounded_2026-11-06.md` (MIR-phase share)

## Symptom
Bootstrap run 14 (`748511468e5`, `build/bootstrap-opus-14`), Stage 2 compiler
tests, row `compiler_cli_build` (8 MIR shards, 2 workers, Cranelift). Both
shard workers lowered MIR cleanly, then grew in native codegen from ~24.2 to
28.7 / 28.1 GiB until the tree hit 60.1 GiB against the 60 GiB cap.

The `native_compile done=13` / `done=19` counters in the log are printed 2 ms
into the phase. They count modules settled before codegen, not objects
written. The cache shows **669 objects written** in the two workers between
08:14:26 and the 08:18:37 kill (of 734 uncached), so the growth was
~4.3 GiB over ~335 modules per worker, **~13 MiB per module**, not 0.3 GiB.
The row died with ~90% of codegen done.

## Cause
`compile_module_with_backend_scoped_v1`
(`src/compiler/70.backend/backend/backend_helpers.spl:411` before this fix,
the `var scoped = ...` line, now :421) opened its per-module transient scope only when
`SIMPLE_CODEGEN_MODULE_SCOPE=1`. Nothing in the bootstrap sets it. The
runtime has no collector, so every module's storage-projection lowering, MIR
optimization copy, Cranelift translation scratch and object byte copy stayed
live until the worker exited. The 2026-10-24 record placed the scope here
(v2, around the pure compile only, outside the session authority writes) but
left it opt-in pending qualification; this record is that qualification.

## Measurements (run-14 Stage 2 candidate `3d49ef45...`, aarch64, `MemoryMax=40G`)
Codegen-only route (`SIMPLE_FILE_WORKERS=0 SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=0`,
`--backend=cranelift --low-memory --threads 1`), sources = the run-14 SCV
snapshot. RSS of the compiler vs objects written:

| closure | N | default (unscoped) GiB | `SIMPLE_CODEGEN_MODULE_SCOPE=1` GiB |
|---|---|---|---|
| `src/app/lint/main.spl` (300 codegen modules) | 10 | 3.52 | 3.17 |
| | 50 | 3.91 | 3.29 |
| | 100 | 4.44 | 3.18 |
| | 200 | 5.72 | 3.43 |
| | 290 | 6.30 | 3.42 |
| | slope | 11.9 MiB/module | 1.9 MiB/module |
| | peak | 6.68 | 3.55 |
| `src/app/stats/main.spl` (69) | slope | 11.0 MiB/module | 3.6 MiB/module |

Projected run-14 shard worker (24.2 GiB at codegen start, ~370 modules):
unscoped ~28.9 GiB (observed 28.7 at ~90%); scoped ~24.9 GiB.

## Fix
`codegen_module_scope_enabled_for_v1(backend_name, knob)`: on for Cranelift
unless `SIMPLE_CODEGEN_MODULE_SCOPE=0`; the other backends keep the explicit
`=1` opt-in (their in-memory lanes, e.g. the `SIMPLE_BOOTSTRAP=1` LLVM string
cache, are not qualified). No new locks; the scope still wraps only the pure
compile and promotes only the returned `Result`.

## Verification
- Policy spec: `test/01_unit/compiler/backend/cranelift_codegen_module_scope_default_spec.spl`.
- Measured check: `scripts/bootstrap/tests/cranelift-codegen-scope-rss-test.shs <compiler>`
  (synthetic 40 x 40-function project, slope threshold 5 MiB/module):
  - RED, run-14 Stage 2 (`3d49ef45...`, no fix): `FAIL — 41 objects, slope 14.7 MiB/module` (20.4 on a second run).
  - GREEN, Stage 2 rebuilt with this fix by the run-14 Rust seed and runtime
    authority (same argv/env as the run-14 Stage 2 command transcript, source
    `748511468e5` + this patch; sha256 `adcee4098386ab69...`):
    `PASS — 41 objects, slope 0.9 MiB/module`. Same binary with
    `SIMPLE_CODEGEN_MODULE_SCOPE=0`: `FAIL — slope 14.7 MiB/module`.
- Rebuilt Stage 2, no env, real lint closure (298 objects): RSS 3.30 GiB at
  N=10, 3.32 at N=100, 3.39 at N=200, 3.35 at N=290; slope 1.8 MiB/module,
  peak 3.58 GiB (run-14 binary: 11.9 MiB/module, peak 6.68 GiB). Objects
  per module identical to the run-14 binary's except the same 2
  nondeterministic modules below.
- Independent Opus review: no blocking code finding; module-level globals on
  the Cranelift path audited (auto-vectorize memo pre-warmed, SIMD provider
  report unreachable, K1 tables installed at startup). Script hardened per
  review (asserts serial in-process codegen, INT/TERM cleanup).
- Object identity: stats closure 69/69 modules byte-identical (paired by
  capsule receipt module name); synthetic 41/41 identical; lint closure
  296/298 identical. The other 2 (`lib.common.sdn.value`,
  `compiler.common.assurance.policy_schema`) also differ between two
  UNSCOPED default runs: their capsule MIR digest changes run to run (the
  enum-identity constant folds a symbol id), so the input differs before any
  codegen scope opens. Pre-existing MIR nondeterminism, not caused by this fix.
- `src/compiler/bootstrap_admission/p2_add.spl` (the module that SIGSEGV'd
  under the v1 placement) builds and prints 5 with the scope on; zero
  `[codegen-scope]` warnings in every scoped run.
