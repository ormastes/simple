# CudaExec cannot back `jit(remote(cuda(...)))` cells yet — no per-cell PTX compile path
**Status:** OPEN (unverified 2026-09-12)

Date: 2026-08-08
Found by: Task K5 (`CudaExec` notebook lane)

## Summary

`doc/05_design/app/tools/notebook_lanes_architecture.md` §4.4 says
`jit(remote(cuda(...)))` cells are "allowed; each cell body must be a
complete kernel program" — implying each cell's Simple `@gpu("cuda")` source
is lowered (frontend → HIR → MIR → `CudaBackend`) and launched fresh per
cell, with state sharing only through explicit arena reads/writes.

The only landed JIT-lane executor, `src/lib/gc_async_mut/gpu_lane/cuda_jit_lane_executor.spl`
(Task B2), does implement that real compile pipeline (`lower_vector_add_ptx`
→ `validate_ptx_artifact` → `CudaLaneSession.load_entry` → `launch_once`),
but it is hardcoded to ONE fixed kernel (`vector_add_kernel_source()`), not
the caller's cell text — `run_program(blob)` only varies the numeric vector
length, never the compiled program. There is no landed path that takes an
arbitrary notebook cell's Simple source and produces a validated PTX
artifact + launch for it.

## Impact

`src/lib/nogc_sync_mut/notebook/cuda_exec.spl`'s `CudaExec` only implements
the `interpreter(remote(cuda(...)))` SVM-G lane (Tasks B3/B4, which K5
explicitly depends on). For a `jit(remote(cuda(...)))` mode spec,
`CudaExec.probe()` and `CudaExec.execute_cell()` both return an honest
`blocked:`/error diagnostic pointing at this file rather than silently
running the fixed vector_add kernel regardless of cell content (which would
be worse — a cell's code would appear to "run" while being ignored).

## Suggested fix

Generalize `cuda_jit_lane_executor.spl`'s pipeline (or add a sibling) that
takes arbitrary `@gpu("cuda")` cell source instead of the fixed
`vector_add_kernel_source()`, then wire `CudaExec` to it for the `jit` base
runtime.

## Files

- `src/lib/gc_async_mut/gpu_lane/cuda_jit_lane_executor.spl` (fixed-kernel JIT executor)
- `src/lib/nogc_sync_mut/notebook/cuda_exec.spl` (`probe`/`execute_cell` jit-base-runtime branch)

## Verification 2026-08-17 (content classification) — LIVE, but fails LOUDLY

Confirmed live in `src/lib/nogc_sync_mut/notebook/cuda_exec.spl`. The jit lane is
not silently wrong — it is explicitly gated and names this doc in its own error
strings: `LaneStatus.Blocked(...)` at line 134, `blocked_reason` at 140, and
`cell_result_error(...)` at 175, each triggered by `if self.base_runtime ==
"jit"`. The header comment (39-46) states the gap directly.

Classification note for the silent-wrong-result sweep: this row does **not**
belong to that class. It returns an honest error rather than a wrong answer, so
it is a feature gap (per-cell Simple->PTX compile path missing), not a
correctness defect. Only `KERNEL_PTX_PATH` (line 60), a checked-in fixed kernel
artifact, ever executes.

Not proven: no `Results:` line — CUDA hardware lanes were not exercised.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Triage 2026-09-13

Confirmed still live: `src/lib/nogc_sync_mut/notebook/cuda_exec.spl` still gates the `jit` base runtime with an honest `LaneStatus.Blocked`/error diagnostic naming this doc (grep confirms `blocked_reason`/`cell_result_error` call sites unchanged since the 2026-08-17 verification). This is a feature gap (a per-cell Simple->PTX JIT compile pipeline generalizing `src/lib/gc_async_mut/gpu_lane/cuda_jit_lane_executor.spl` beyond its single fixed `vector_add_kernel_source()`), not a correctness defect — it already fails loudly rather than silently. Implementing the generalized pipeline is multi-file, CUDA-hardware-dependent feature work well beyond this pass's per-bug budget (no CUDA hardware confirmed available in this triage to prove a fix `Results:` line either). Leaving OPEN, no code change made this pass; direction unchanged from the existing "Suggested fix" section.
