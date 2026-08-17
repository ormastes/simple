# JIT: layout_run_full_with_ports dies with nil-receiver field access (core dump)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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

## Triage 2026-08-17 (lane m7c_lib_async) — UNVERIFIED on this host

The defect is a JIT-only nil-receiver fault. A spec body runs INTERPRETED, so it can never go red from a spec alone, and the CUDA execution port needs GPU hardware absent from this host. Not reproduced and not closed: this lane could neither exercise the path nor
find content-level evidence of a fix. Recording UNVERIFIED explicitly so it is
not mistaken for either a live confirmation or a close.

### Location correction (lane m7c_lib_async, 2026-08-17)

The triage row pointed at
`src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/cuda_execution_port.spl`,
but `layout_run_full_with_ports` is not defined there. It is defined at
`src/lib/common/structural/layout/engine.spl:664` (self-call at :681, exported
at :698), re-exported through `src/lib/common/structural/layout/__init__.spl:31`,
and consumed by
`src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/manager.spl:11`.
Anyone picking this up should start at `common/structural/layout/engine.spl`,
which is a different owner's file scope than the row implied.
