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

## 2026-11-05 verification evidence (worktree work/libbug-w7-iort-20261105, aarch64 Linux with working software Vulkan (lavpipe) lane, host phase1_1793422538 simple CLI, interpreter mode)

Commands and results:

1. `simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_owner_state_spec.spl --mode=interpreter --clean` → **OK, 3/3 passed**. The 2026-11-03 owner-result candidate (`Engine2dDrawIrAdvOwnerResult` batch/composition owner paths, receipt snapshots, composition-to-retained-damage lineage, legacy readback continuation) now has real behavioral results on a qualified host. The candidate behaves as documented; the previously TEST_BLOCKED gate is unblocked.
2. `simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl --mode=interpreter --clean` → was **68/70**; now **69/70** after two repairs (below). The remaining failure is diagnosed and reported verbatim in item 5.

3. Repair A — spec regression (not a source bug): "submits a GPU-selected Draw IR batch through the runtime host GPU queue" failed because the spec called `engine2d_host_gpu_runtime_queue("vulkan", 7, true, 4096)` (backend_handle = 0), which the submit path rejects (`invalid_backend_handle`). Commit 88aac2ffe28 ("rebase(main): transplant current main tree onto release/1.0") had clobbered the hardened version from 44e23835577 ("fix(gui): harden host gpu runtime queue evidence"), which uses `engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 7, 7, true, 4096)` and pins `unit_id == "runtime-batch-runtime"`. Restored both lines → test green.

4. Repair B — genuine source bug (TDD attempt 1 of 4): "stages retained Vulkan composition damage for a partial host refresh" failed because the retained-damage executors in `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` called `eng.present()` BEFORE `eng.read_pixels_with_source()`. Probe evidence: on a live Vulkan lane, `present()` rotates to a fresh back buffer, so the readback returned the cleared frame (all background pixels; `vulkan_present_readback_bytes()` = 48 for a full refresh of an empty surface). This violates the backend's own documented contract (backend_vulkan.spl present(): "draw_ir_adv reads pixels BEFORE present"). Fixed the three identical sites (`engine2d_draw_ir_render_damaged_with_images`, `_engine2d_draw_ir_render_prepared_damage_plan_with_images`, `_engine2d_draw_ir_render_composition_damaged_with_images`) to read back first, then present. Verified: the damaged pixel now reads back RED on both Vulkan and CPU lanes; no regressions (`draw_ir_owner_state_spec` 3/3; `draw_ir_v4_legacy_rejection_spec` 2/4 and `engine_vulkan_present_api_spec` 0/2 fail identically WITHOUT the change — pre-existing).

5. Remaining failure (reported verbatim, NOT fixed): the same Vulkan test now fails one assertion later — `expected 48 to equal 4` at the pinned `engine.vulkan_present_readback_bytes() == 4` oracle. Diagnosis: the replayed display list contains a full-surface background rect, so the Vulkan frame-damage union legitimately covers the whole 4x3 surface and the honest receipt reports a full-surface download (48 bytes). A 4-byte damage-scoped receipt would require the draw funnel to intersect damage hints with the staged damage clip, which backend_vulkan.spl deliberately rejects ("An active clip can only SHRINK the painted area, so ignoring it keeps the union conservative (a superset), which is the safe direction"). On hosts without a real Vulkan device the test body is skipped (`if engine.backend_name() == "vulkan"`), so this oracle has very likely only ever been green vacuously. This is a requirement-vs-implementation receipt gap, separate from the caller-visible-mutation semantics this bug tracks; fixing it needs an owner decision on the receipt contract, not a verification-lane change.

Status note: bug_db.sdn intentionally NOT modified (verification-only mandate). The bug doc's own guidance applies: keep open until the candidate is merged and behavioral gates are green; gate 1 (owner-state spec) is now green, the repro spec is 69/70 with the residual oracle gap documented above.
