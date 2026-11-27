# SDN-roundtripped Draw IR composition fails render: "cannot assign field on non-object value"

- **Date:** 2026-08-15
- **Status:** RESOLVED 2026-08-15 (see "RESOLVED" section below; header corrected 2026-11-25 — it previously still read OPEN)
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

## Verification 2026-11-25 (release/1.0.0, Windows lane)

Confirmed the resolution is real at release/1.0.0 HEAD (`8aa26f51e72`):

- The ClassInstance arms for field assignment are present in the pinned seed's
  interpreter source: `src/compiler_rust/compiler/src/interpreter/node_exec.rs`
  (`Value::ClassInstance(instance) => { ... instance.set_field(...) }` for both
  the local-env and MODULE_GLOBALS paths, ~lines 1602-1608 and 1640-1649).
- Live probe through the pinned binary (`bin/simple.exe`, v1.0.0-rc.1,
  build-commit 1343b77bbaa): a class-with-class-field program performing
  `o.inner.x = 42` and `o.name = "b"` prints `nested=42 name=b` — nested field
  assignment on ClassInstance values works end-to-end.
- Limit: `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl`
  itself could not be re-run in this environment — release/1.0.0 HEAD carries
  940 `@representation_boundary` annotations (commit cfd89933699) that the
  pinned seed rejects (`unknown decorator`), so `bin/simple.exe test` fails
  repo-wide before reaching any spec body. The 4/4 result recorded on
  2026-08-15 plus the source and probe evidence above is the basis for this
  closure.
