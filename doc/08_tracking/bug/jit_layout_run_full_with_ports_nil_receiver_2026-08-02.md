# JIT: layout_run_full_with_ports dies with nil-receiver field access (core dump)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

**Revalidated 2026-11-02: still plausible because the report title (layout_run_full_with_ports core-dumps on nil-receiver field access under JIT) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## Revalidation 2026-11-03 (still reproduces; Rust-seed JIT defect, not a Simple-source defect)

Seed `bin/simple.exe run` (default JIT) on the probe below exits **rc=139 (segfault)** with no output; with
`SIMPLE_EXECUTION_MODE=interpreter` it prints `boxes=2 backend=serial_cpu`. So the divergence is real, but
the library code is correct under the interpreter; the fault is in seed Cranelift codegen for the trait-object
port dispatch inside `_layout_snapshot_with_ports` (`src/lib/common/structural/layout/engine.spl:664`). Fix needs a
Rust seed change + redeploy, so it is not fixable from `src/lib`. Note: a probe that omits `layout_input` defaults
is demoted to the interpreter by `[jit-fallback]` (call-site-constant default rule) and does not crash - pass the
named `oracle_boxes:` argument as below to stay on JIT.

```simple
use std.common.structural.layout.*
fn main():
    val nodes = [layout_node(1, 0, "block", true, false, 0, 40, false, layout_node_semantics_default("block")),
                 layout_node(2, 1, "block", true, false, 0, 10, false, layout_node_semantics_default("block"))]
    val prof = layout_execution_profile("hybrid_vector_gpu", 100, 40, 20, 1024, 1024, 2, 10, 5)
    val inp = layout_input(nodes, [], [], prof, 4, oracle_boxes: [layout_box(1, 0, 0, 640, 480), layout_box(2, 8, 8, 624, 32)])
    val snap = layout_run_full_with_ports(inp, layout_text_measure_port_unavailable(), layout_execution_port_oracle(inp.oracle_boxes), layout_execution_port_unavailable("hybrid_vector_gpu", "gpu-x"))
    print "boxes={snap.boxes.len()} backend={snap.backend}"
main()
```

Status stays open; owner = seed JIT codegen (needs `SIMPLE_JIT_STRICT`/Cranelift trait-object dispatch triage on a
rebuilt seed). Also stale: `test/03_system/platform/structural_compute/layout_framework_spec.spl` calls `layout_node`
with 10 args (9 expected) and `fixture_node` is undefined, so it cannot serve as the regression spec yet.
