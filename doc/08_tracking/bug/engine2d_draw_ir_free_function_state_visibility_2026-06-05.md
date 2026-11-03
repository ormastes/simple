# BUG: Engine2D Draw IR executor cannot rely on caller-visible free-function mutation

Status: open

- id: engine2d-draw-ir-free-function-state-visibility
- date: 2026-06-05
- area: rendering / engine2d / draw-ir
- severity: medium
- status: open

## Summary

The new Draw IR advanced executor must return pixel readback evidence directly
from the execution result. In focused tests, relying on a free function to mutate
an `Engine2D` argument and then reading pixels from the caller-owned engine is
not reliable enough to prove rendering happened.

## Impact

GPU backend hardening and Draw IR parity tests need unambiguous readback
evidence. If tests rely on caller-visible mutation only, a backend could draw
into a local execution context while the caller reads stale pixels and the test
would either fail incorrectly or mask the real state boundary.

## Current Mitigation

`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` returns `pixels` in
`Engine2dDrawIrAdvResult`. The focused Draw IR executor tests assert those
returned pixels instead of assuming caller-visible mutation.

## Fix Direction

Clarify or fix Simple value/mutability semantics for this pattern:

- decide whether backend executor functions should take an explicitly mutable
  engine/session handle;
- add a minimal language/runtime test proving caller-visible mutation for
  engine-like structs, or document that executors must return readback evidence;
- once semantics are stable, simplify Draw IR executor tests only if the caller
  state readback becomes reliable.

## Reproduce

Use the Draw IR executor path and compare readback from the returned
`Engine2dDrawIrAdvResult.pixels` with readback from the original caller-owned
engine after the free function returns.

Focused verification currently passing with the mitigation:

```
bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl --mode=interpreter --clean
```

## 2026-11-03 owner-result candidate

The historical command above is prior evidence, not a verification of this
candidate. Ordinary batch and composition execution now expose
`Engine2dDrawIrAdvOwnerResult`, containing the actual final `engine` and the
existing `result` receipt. Callers continue with `owned.engine`; they do not
infer retained backend/font/frame state from a pixel array or from argument
aliasing. Both Screen2d showcase hosts adopt the returned owner even when the
receipt is rejected, so partial execution cannot leave their retained owner
stale.

Receipt-only APIs retain their prior signatures and behavior. In particular,
legacy composition CPU framebuffer writeback remains confined to the legacy
path. The explicit owner path presents its final engine directly and does not
perform that writeback. This is an explicit ownership contract, not a claim
that compiler value/alias semantics have been repaired.

Three authored regressions in `draw_ir_owner_state_spec.spl` cover batch
continuation and receipt snapshots, composition-to-retained-damage lineage,
and legacy readback plus empty-composition continuation. Behavioral execution
is **TEST_BLOCKED** because no qualified self-hosted full CLI is available on
this Windows host. The Rust seed is not used as ordinary verification. Keep
this bug open until the required behavioral gates have real results and the
candidate is merged.
