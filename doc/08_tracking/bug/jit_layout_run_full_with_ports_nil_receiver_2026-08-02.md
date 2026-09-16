# JIT: layout_run_full_with_ports dies with nil-receiver field access (core dump)

**Date:** 2026-08-02 · **Severity:** medium · **Area:** Cranelift JIT / gpu_web layout ports

## Symptom

Calling `layout_run_full_with_ports` under the default JIT engine
(`bin/simple run`, no execution-mode override) crashes with
`runtime error: field access on nil receiver` and a core dump. The SAME
input runs correctly under the tree-walk interpreter
(`SIMPLE_EXECUTION_MODE=interpreter`).

## Context

Found while probing the CUDA layout execution port
(`src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/cuda_execution_port.spl`).
Related JIT divergences hit in the same probe session:

- `CudaSession.init()` returns 1 under JIT while the interpreter initializes
  headless CUDA fine (rc=0 on RTX A6000 + TITAN RTX) — so the CUDA layout
  lane reports `cuda-layout-init-failed` only under JIT.
- The deployed binary's extern registry predates
  `rt_write_u32s_to_raw_checksum` (`src/lib/nogc_sync_mut/ptr/raw.spl:13`),
  so the port cannot execute under the deployed interpreter either —
  bootstrap rebuild + redeploy required (extern additions need rebuild).

Enablement plan for the whole lane:
`doc/03_plan/ui/rendering/cuda_layout_port_enablement_plan.md`.

## Repro

Probe scripts (session scratchpad copies): construct a small
`LayoutExecutionRequest` (2-leaf block batch) and call
`layout_run_full_with_ports` via `bin/simple run` — crash; identical run
with `SIMPLE_EXECUTION_MODE=interpreter` completes.

## Status

Open. Engine-divergence family
(`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`).
