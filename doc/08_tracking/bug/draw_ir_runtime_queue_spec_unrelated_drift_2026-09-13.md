# `draw_ir_runtime_queue_spec.spl` has 2 unrelated failures, discovered while re-checking a different bug

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
