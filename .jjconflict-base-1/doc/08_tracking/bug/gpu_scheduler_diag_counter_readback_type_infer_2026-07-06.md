---
id: gpu_scheduler_diag_counter_readback_type_infer_2026-07-06
status: OPEN
severity: medium
discovered: 2026-07-06
discovered_by: GPU event/job scheduler std.diag instrumentation spec authoring
related: src/lib/nogc_sync_mut/diag.spl
related: test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl
---

# Interpreter: `Dict<text,i64>.get(k) ?? <i64>` mis-infers key type on first monomorphization

## Summary

When a `Dict<text, i64>.get(key) ?? <i64-default>` expression is the FIRST
occurrence of that generic instantiation to be monomorphized in an interpreter
process, the checker infers the `.get(...)` result as the KEY type (`text`)
instead of the VALUE type (`i64`), then rejects the `??` coalesce with
`text` against the `i64` default:

```
semantic: type mismatch: comparing string with integer
```

This is order-dependent: `test/01_unit/lib/nogc_sync_mut/diag_spec.spl` exercises
the exact same std.diag functions and passes, but only because earlier `it`
blocks in that file happen to warm the monomorphization first. In a fresh spec
that touches the path as first-toucher, the same call fails.

## Affected std.diag paths (all use `Dict<text,i64>.get(k) ?? <i64>`)

- `dbg_counter_value(label)` — `_g_counters.get(label) ?? 0` (diag.spl:334)
- `dbg_summary()` — `_g_counters.get(label) ?? 0` (diag.spl:352)
- `dbg_stage(component, stage)` — `_g_stage_last_ms.get(component) ?? now`
  (diag.spl:150). Because this runs whenever the `stage` OR `watchdog` facet is
  enabled, simply turning on the stage facet from a fresh process trips the bug.
- Reading `dbg_stage_history()[i].stage` (a `[StageEntry]` element field access)
  reproduces the same class of first-monomorphization mis-inference.

Safe paths (no `Dict.get ?? i64`): `dbg_event_hop` (pure text), `dbg_last_emit`,
`dbg_deadline_active_count`, and the all-facets-off early-return branches.

## Reproduction (minimal)

```simple
use std.spec.*
use std.diag.{dbg_diag_reset, dbg_counter_value}
describe "repro":
    it "counter read-back":
        dbg_diag_reset()
        expect(dbg_counter_value("nope")).to_equal(0)   # -> comparing string with integer
```

## Impact

- Not a defect in the GPU scheduler instrumentation itself: the scheduler's
  `dbg_count("host_gpu.*")` writes and `dbg_stage("gpu_queue", ...)` calls compile
  and run; only the interpreter READ-BACK / stage-facet-enable path is blocked.
- `test/02_integration/lib/gpu/gpu_scheduler_diag_spec.spl` therefore asserts the
  instrumentation through the safe `events`/hop text path (dbg_last_emit), which
  already carries the count evidence (queued=1/submitted=1/completed=1/drained=1).
  The stage-line labels and `dbg_counter_value`/`engine2d_host_gpu_diag_summary`
  read-back could not be asserted directly.

## Next Steps

- Fix generic monomorphization ordering in the interpreter so `Dict<K,V>.get(k)`
  always resolves to `V` (here `i64`) regardless of first-touch order, so the
  `?? <default>` coalesce type-checks against `V`.
- Once fixed, re-enable stage-facet + counter/summary assertions in the GPU
  scheduler diag spec (and drop the warmup dependency in diag_spec).
