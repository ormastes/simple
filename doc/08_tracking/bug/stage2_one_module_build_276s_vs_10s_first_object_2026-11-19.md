---
id: stage2_one_module_build_276s_vs_10s_first_object_2026-11-19
status: open
severity: high
discovered: 2026-11-19
discovered_by: xc phase-2 WSL rebuild (release/1.0.0 eb20b33db6a)
related: scripts/bootstrap/bootstrap-from-scratch.sh (COMPILER_BUILD_TIMEOUT_SECONDS, default 180, line ~2340)
related: src/compiler/bootstrap_admission/p2_add.spl
---

# Stage 2 compiler needs 276 s to build a 1-module program (target: first object in 10 s)

## Symptom
Phase-2 bootstrap (WSL Ubuntu-24.04, 64 GB, 12 jobs) built Stage 2 in 2584 s, then
Stage 2 sanity aborted: `sanity FAIL - frontend smoke exited 124`, log
`bounded-log-error: timeout`, `timeout_seconds=180`. The abort message pointed at
`bootstrap_stage2_empty_mir_bodies_2026-07-05` — misleading.

## Diagnosis (not a hang, not empty MIR)
Running the rejected stage2 binary directly on `p2_add.spl`
(`native-build ... --backend llvm`, 1500 s timeout) finished rc=0 in **276 s**,
~2.4 GB peak RSS, one core busy. The output binary printed `5` (correct), so MIR
bodies are real. The 180 s sanity timeout is simply below the real cost.

## Measured breakdown (1 module)
- ~16 s source loading (`phase=load_sources`) on EVERY worker re-entry
  (`[coordinator-route]`/`[positional-route]` restarts), repeated per child.
- HIR/MIR for the single module: ~13 s / <1 s (`elapsed_ms` 16-30 s).
- ~200+ s in native compile + link after `phase=native_compile`, with the log idle.
Owner target: first object within 10 s per file (memory: first-object-in-10s).

## Workaround
`COMPILER_BUILD_TIMEOUT_SECONDS=900` (env knob) — used for the rerun.

## To do
- Profile native_compile/link for a 1-module build; remove per-re-entry source reload.
- Repro/regression: perf budget spec for p2_add native-build (target <=10 s first object).
- Also: abort pointer in bootstrap-from-scratch.sh corrected (this PR).
