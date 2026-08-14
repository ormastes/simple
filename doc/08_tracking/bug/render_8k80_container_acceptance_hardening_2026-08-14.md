# Render 8K80 container acceptance hardening gaps

Status: **OPEN / FINAL REVIEW REJECTED AFTER THREE FIX CYCLES**

The container/GPU research and design are complete, and substantial source
implementation exists, but independent review rejected the handoff. No A4,
A5, or A7 acceptance item may be promoted from this source-only state.

## Checker and provenance gaps

- The checker applies A4's 20-revision/256x128 workload hash to A5's distinct
  60-sample semantic workload. Give each lane its own workload hash and
  correlate them with a separate campaign ID.
- A4 validation omits the exact considered, culled, rendered, and skipped
  command counts required by TODO687.
- Compiler provenance, native-build logs, and the CUDA qualification receipt
  are deleted with the temporary run. Publish and hash these inputs in the
  immutable run set before accepting `container_gpu_admission`.

## Device and process-verdict gaps

- Strict DrawIR submit/fence counts are assigned from aggregate success rather
  than observed backend counters; `submit_batch()` may succeed as a no-op.
  Extend the Vulkan frame receipt with actual submit/fence deltas and require
  those observed values.
- The strict producer's `--out` path returns zero after writing a blocked or
  failed receipt. Preserve the receipt status in the process exit code.
- The physical wrapper does not yet emit the correlated physical receipt
  schema. Full promotion remains TODO684/TODO685.

## Unblock condition

Resolve every item above, extend deliberate-red tests so each former defect is
detected, obtain independent highest-capability acceptance, then run the live
paths with a provenance-admitted Stage 4 compiler. The three-cycle cap for the
current session is exhausted; resume in a fresh scoped session.
