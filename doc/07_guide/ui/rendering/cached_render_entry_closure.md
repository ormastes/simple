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

Canonical plan:
`doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`.
Retained report:
`doc/09_report/drawir_sparse_dynamic_8k_attempt_2026-08-12.md`.
Open blocker:
`doc/08_tracking/bug/self_hosted_cli_native_build_silent_no_artifact_2026-08-14.md`.
