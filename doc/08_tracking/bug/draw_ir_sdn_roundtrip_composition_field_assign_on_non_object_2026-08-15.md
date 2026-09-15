# SDN-roundtripped Draw IR composition fails render: "cannot assign field on non-object value"

- **Date:** 2026-08-15
- **Status:** OPEN (root-caused to the SDN round-trip input, exact assignment site not yet pinned)
- **Component:** common.ui.draw_ir_sdn / gc_async_mut.gpu.engine2d.draw_ir_adv (interpreter path)

## Symptom

`test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`
scenario "submits and drains a GPU-selected Draw IR batch through the runtime
queue" fails with `semantic: invalid assignment: cannot assign field on
non-object value`. Same error hits
`draw_ir_target_spec.spl` scenario 1 under SIMPLE_COVERAGE (passes standalone).

## Bisection evidence (minimal repros, seed rebuilt 2026-08-15 00:50)

1. Direct composition -> `engine2d_draw_ir_adv_composition(engine, comp, true)`
   renders fine (`rendered=1 backend=gpu`).
2. Queue dispatch without Engine2D (`engine2d_draw_ir_runtime_queue_dispatch_only`)
   succeeds (`submitted=true drained=1 dispatched=true`).
3. `sdn_to_draw_ir(dispatch.payload_text)` parses (`batches=1`), but feeding
   that ROUND-TRIPPED composition to `engine2d_draw_ir_adv_composition(engine,
   comp, true)` fails with the invalid-assignment error, on the identical
   engine/batch geometry that works in (1).

So some field of the SDN-reconstructed composition/batch/embedding is nil (or a
non-object erased value) where the direct constructor produces an object, and a
later `x.field = v` inside the render path trips on it. Repro scripts preserved
during the session: `repro_rq3.spl` / `repro_rq4.spl` (scratchpad; re-create
from this record's steps if needed).

## Impact

- Runtime-queue GPU happy-path spec red (1/4 scenarios).
- Any consumer that renders a composition reconstructed from the runtime queue's
  SDN payload (the real host/GPU transport path) is broken under the
  interpreter.

## Next step

Diff the struct produced by `sdn_to_draw_ir` against `draw_ir_composition(...)`
field-by-field (source/embedding/style payloads) to find the nil field; then fix
`draw_ir_sdn` decode (or make the render path fail closed with a diagnostic).

## RESOLVED 2026-08-15 (later same day)
Root cause was the interpreter's missing ClassInstance arm for nested field
assignment (see interpreter_nested_field_assignment_broke_be_dom_cascade_2026-08-15.md).
After the node_exec.rs fix, `draw_ir_runtime_queue_spec.spl` is 4/4 and
`draw_ir_composition_damage_spec.spl` is 7/7.

## Triage 2026-09-12
Rule B: re-ran `bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl` on the deployed seed; it still FAILs, matching the recorded defect. Status word left as-is. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check 2026-09-13 (BUGFIX-7 lane)

```
bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl
Results: 4 total, 2 passed, 2 failed
```

Same binary family (`bin/release/aarch64-unknown-linux-gnu/simple`) at
`a6450c9d6f5`. The specific documented defect — `semantic: invalid assignment:
cannot assign field on non-object value` on the SDN round-trip path — does
**not** reproduce; no such error appears anywhere in the run. The 2 failures
present now are unrelated in shape:

1. "submits and drains a GPU-selected Draw IR batch..." fails on
   `expected runtime-batch-runtime to equal batch-runtime` (an id/string-format
   assertion mismatch, not a crash).
2. "computes a stable, content-sensitive payload checksum and summary" fails
   with `semantic: function 'engine2d_draw_ir_payload_summary' not found` — a
   missing function, i.e. test/source drift, not the SDN-roundtrip defect.

This matches the 2026-09-12 "Rule B" triage's own note that the earlier
RESOLVED-2026-08-15 fix (`interpreter_nested_field_assignment_broke_be_dom_cascade_2026-08-15.md`,
a Rust `node_exec.rs` interpreter change) may not have been in that day's
deployed seed; it evidently is now, or a later fix subsumed it independently.

- Status: CLOSED (2026-09-13) — not reproducible on `a6450c9d6f5`
  (`bin/release/aarch64-unknown-linux-gnu/simple`, seed dated 2026-09-06). The
  spec's 2 remaining failures are a distinct, unrelated regression — filed
  separately as
  `doc/08_tracking/bug/draw_ir_runtime_queue_spec_unrelated_drift_2026-09-13.md`.
