# CUDA layout port — audit result and enablement plan (2026-08-02)

## Status: wiring ALREADY EXISTS but the CUDA lane is data-starved; the port itself
cannot execute on this host in any currently-runnable engine. No src edits made.

## Port contract (src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/cuda_execution_port.spl)
- NOTE: the audit path `gpu/gpu_web/cuda_execution_port.spl:389-433` is stale; real
  path is `gpu/browser_engine/gpu_web/layout/cuda_execution_port.spl` (532 lines).
- Computes the exact browser layout slice for one-level islands of fixed-px leaf
  children: 3 PTX kernels — `web_layout_fixed_children` (block stacking / flex
  row-column / grid track placement), `web_layout_absolute` (absolute inset
  resolution vs parent box), `web_layout_overflow` (per-container scrollable
  overflow max). Profiles admitted: block, flex, grid, absolute-sticky, scroll.
- Input: `LayoutExecutionRequest` (input.nodes + grid_tracks, islands,
  selected_island_ids, candidate_backend). Packs 13 u32 words/node, launches with
  block size 256, reads back 5 output + 7 overflow words/node.
- Output: `LayoutIterationResult` {boxes, fragments("principal"), overflows,
  proof, fault}. Proof fields: candidate_backend, executed_backend
  ("hybrid_vector_gpu"), executed/submitted/synchronized/device_readback,
  oracle_verified (boxes compared against constructor-supplied `oracle_boxes`),
  reason (= fault string).
- ~25 admission fault reasons (e.g. `cuda-layout-fixed-size-required`,
  `cuda-layout-one-level-required`, `cuda-layout-batch-heterogeneous`) +
  runtime faults (`cuda-layout-init-failed`, `-upload/submit/sync/readback-failed`,
  `cuda-layout-oracle-mismatch`). Fails closed in every case.

## Why the render-session CUDA lane never runs (probe-proven)
Wiring exists: simple_web_render_session.spl:355-364 passes
`web_cuda_layout_execution_port([])` into `web_layout_manager_run_*_with_ports`
→ manager.spl:_web_layout_run → engine.spl:_layout_snapshot_with_ports, which IS
the GPU-first-with-CPU-fallback policy (engine.spl:563-593). But:
1. engine.spl:565 gates GPU on `input.oracle_boxes.len() > 0`; the session adapts
   via `web_layout_adapt_prepared` → include_oracle=false (adapter.spl:463 routes
   oracle boxes to retained_* fields) → reason `gpu-oracle-unavailable`, CPU port
   runs. Probe (interpreter): executed_backend=serial_cpu, fault="", reason
   verbatim `gpu-oracle-unavailable`.
2. Session constructs the port with `[]` oracle, so even if gated in, the port's
   own verify would emit `cuda-layout-oracle-mismatch`.

## Why the port itself is broken on this host
- Interpreter (only lane where CUDA inits: session probe init rc=0, activate rc=0
  on RTX A6000 + TITAN RTX): `error: semantic: unknown extern function:
  rt_write_u32s_to_raw_checksum` — deployed bin/simple's extern registry predates
  this extern (declared in src/lib/nogc_sync_mut/ptr/raw.spl:13; present in
  generated runtime_symbol_entries.rs). Needs a bootstrap rebuild + redeploy.
- JIT (default): direct port.execute runs, admission PASSES for a 2-leaf block
  batch, but CudaSession.init() returns 1 → proof.reason verbatim
  `cuda-layout-init-failed` (known JIT/interpreter CUDA divergence).
- Separate defect found: `layout_run_full_with_ports` under JIT dies with
  `runtime error: field access on nil receiver` + core dump (same input works
  under interpreter). Worth its own bug.

## Enablement steps (in order, NOT done — each >40-line-equivalent or infra)
1. Rebuild bootstrap + redeploy so the interpreter registers
   `rt_write_u32s_to_raw_checksum` / `rt_write_fill_u32s_to_raw_checksum`.
2. Root-cause JIT CudaSession.init()==1 divergence (or pin layout to interpreter).
3. Feed the oracle: either construct the session port as
   `web_cuda_layout_execution_port(adapted.snapshot.retained_boxes)` AND relax the
   engine gate to accept retained boxes as GPU oracle in retained mode, or adapt
   with include_oracle=true for the GPU attempt. Policy decision, not a 2-liner.
4. Re-verify with SIMPLE_TIMEOUT_SECONDS=3600 bin/simple test
   test/03_system/gui/web_showcase_full_gpu_offload_spec.spl --timeout 1700 (13/13).

## Probes (rerunnable)
- scratchpad/cuda_port_probe.spl — direct execute + engine path + session shape
- scratchpad/cuda_session_probe.spl — CudaSession init/activate per engine
- scratchpad/checksum_extern_probe.spl — isolates the missing extern
