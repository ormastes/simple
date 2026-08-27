# Cached Render Entry Closure

`CachedRenderEntryClosureV1` is the planned production-evidence workflow for
the sparse DrawIR 8K benchmark. It is currently **blocked**: no source-matched, provenance-admitted
Stage 4 CLI is deployed, and the unadmitted artifact under `release/` exits 248
for source execution and returns 0 without an artifact for native-build.

The workflow has four operator steps:

1. **Admit the exact Stage 4 CLI.** Build a full CLI, run the exact candidate
   through the redeploy and essential-tools gates, deploy atomically with a
   rollback receipt, then validate the deployed hash lineage. A Rust seed,
   Stage 3 compiler, stale copy, help output, or missing receipt is not admission.
2. **Build the cached sparse DrawIR carrier.** Using only that admitted CLI,
   first build/run a minimal one-binary entry closure and prove the
   missing-output negative gate. Then build
   `test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl` with explicit source
   roots, LLVM, `core-c-bootstrap`, a fresh stable cache, and a fresh output.
3. **Execute the retained 8K damage corpus.** Run the compiled carrier directly
   under `/usr/bin/time`; do not execute raw source or substitute the bootstrap
   interpreter/native-C operation harness.
4. **Validate identity, correctness, and budget receipts.** Require binary and
   source hashes, actual execution mode, backend/fallback, 7680x4320 viewport,
   20 frames, one 256x128 changing rectangle, two considered and 512 culled
   commands per frame, nonzero readback, zero mismatches, stable checksum,
   valid receipts, executor p50/p95 each no greater than 12.5 ms, and max RSS.

The result is executor-only. It does not prove presentation, physical scanout,
Web/GUI/WM end-to-end throughput, or full-frame CPU 8K/80. Verify each changed
gate once and stop after three distinct fix/verify cycles.

## Fail-closed worker runtime selection

The lightweight `native-build` wrapper no longer falls back implicitly to
`bin/simple` or `src/compiler_rust/target/bootstrap/simple`. It considers only
existing `SIMPLE_BINARY`, `SIMPLE_BIN`, and invoking-executable candidates, in
that order, and rejects canonical Rust-seed paths. When no allowed candidate
remains, preflight returns nonzero before `SIMPLE_BINARY` is exported or a
worker process is spawned.

This is source completion for the focused TODO686 selection criterion, not
runtime admission. Explicit or invoking candidates still require independent
path/hash/stage/provenance qualification. The only admitted local Stage 2 lacks
`test`/`sspec-maintain`/`spipe-docgen`; the available full CLI is known-bad and
unadmitted. Therefore the future-executable SSpec at
`test/03_system/check/cached_render_entry_closure_runtime_selection_spec.spl`
remains BLOCKED-RUNTIME and no Rust-seed result may promote it.
Its verification status is therefore `TEST_BLOCKED`, not PASS.

Canonical plan:
`doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`.
Retained report:
`doc/09_report/drawir_sparse_dynamic_8k_attempt_2026-08-12.md`.
Open blocker:
`doc/08_tracking/bug/self_hosted_cli_native_build_silent_no_artifact_2026-08-14.md`.

Modern contract coverage:
`test/03_system/check/cached_render_entry_closure_contract_spec.spl`, with its
focused runtime-selection companion under the same `test/03_system/check/`
directory, and their operator plan at
`doc/03_plan/sys_test/cached_render_entry_closure.md`. TODO686 owns the CLI fix,
TODO687 owns native 8K evidence, and TODO688 owns admitted self-hosted SSpec,
maintenance, and docgen evidence.
