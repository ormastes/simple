# `draw_ir_runtime_queue_spec.spl` has 2 unrelated failures, discovered while re-checking a different bug
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Found by: BUGFIX-7 lane while re-checking
  `draw_ir_sdn_roundtrip_composition_field_assign_on_non_object_2026-08-15`
  (that record's own defect does not reproduce; these two do).
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed), sha256
  prefix `3d120a6f`, dated 2026-09-06 09:59, at commit `a6450c9d6f5`.
- Spec: `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`

## Repro

```
bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl
Results: 4 total, 2 passed, 2 failed
```

## Failures

1. "submits and drains a GPU-selected Draw IR batch through the runtime queue":
   `expected runtime-batch-runtime to equal batch-runtime` — an id/string
   format mismatch (the actual value has a `runtime-` prefix the expectation
   does not), not a crash.
2. "computes a stable, content-sensitive payload checksum and summary":
   `semantic: function 'engine2d_draw_ir_payload_summary' not found` —
   the function the spec calls does not exist under that name anywhere the
   interpreter can resolve, suggesting either a rename/removal upstream of the
   spec, or the spec was written against a function that was never landed.

## Not investigated further

Out of scope for the lane that found it (busy on a different bug shard).
Needs someone to grep for `engine2d_draw_ir_payload_summary` and its likely
renamed sibling, and to find where the `runtime-` id prefix is added/expected
to reconcile scenario 1.


## Closed 2026-11-10 (fixed spec-side, lane p3-runner3, row 13)

Both failures were spec drift; the implementation is authoritative on both points.

1. `runtime-` unit id prefix: deliberate. `engine2d_draw_ir_payload_summary_sdn_compat`
   (`src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl:172`) builds the
   queue payload SDN as `draw_ir_composition("runtime-{batch.batch_id}", ...)`, so the
   host-fallback render receipt of `engine2d_draw_ir_adv_batch_runtime_queue` carries
   unit id `runtime-<batch-id>`. The sibling authority spec
   `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl:1407` already
   asserts exactly `to_equal("runtime-batch-runtime")`.
2. Function rename: `engine2d_draw_ir_payload_summary` was renamed to
   `engine2d_draw_ir_payload_summary_sdn_compat` (same `(batch, packet_bytes)`
   signature and result fields). The stale name had exactly one remaining caller:
   this spec. The nogc_async_mut twin spec
   (`test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`)
   already uses the `_sdn_compat` name throughout.

Fix (this lane, spec file only): import + call `engine2d_draw_ir_payload_summary_sdn_compat`,
and expect `result.render.unit_id == "runtime-batch-runtime"`.
Verified with the worktree seed-smoke binary (bin/simple.exe, v1.0.0-rc.1):
`draw_ir_runtime_queue_spec.spl` 4/4 PASS (`--mode=interpreter`).
Sibling `draw_ir_adv_spec.spl` 69/70 — its 1 failure ("stages retained Vulkan
composition damage", expected 48 to equal 4) is pre-existing, identical with the
fix stashed and unstashed.
