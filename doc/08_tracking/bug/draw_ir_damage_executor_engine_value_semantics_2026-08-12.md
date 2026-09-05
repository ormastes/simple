# DrawIR retained-damage executor loses Engine2D mutation across helper boundary

Status: CPU RESOLVED / VULKAN TRANSFER OPEN (2026-08-12)

## Symptom

A damage-aware DrawIR executor was prototyped by threading exact disjoint
`DrawIrRect` clips through `_engine2d_draw_ir_render_batch_embedded`. Command
accounting reported the expected executions (two commands for two clips), but
the caller's persistent CPU Engine2D framebuffer remained unchanged. An empty
damage plan correctly executed zero commands. Invalid damage correctly selected
the full-render accounting path, yet its framebuffer mutation was also lost.

The stable boundary is now
`Engine2dDrawIrCompositionDamageOutcome.engine`: callers explicitly install
the authoritative returned Engine2D instead of assuming mutation crossed the
value-semantic helper boundary. WM uses that ownership contract.

## Evidence

- Exact planner: `damage_tiles_spec.spl` 11/11 PASS.
- Exact coalescer: `damage_plan_spec.spl` 11/11 PASS.
- Composition delta: `composition_damage_spec.spl` 4/4 PASS.
- Conservative occlusion: `chunk_occlusion_spec.spl` 4/4 PASS.
- `draw_ir_damage_replay_spec.spl`: 3/3 PASS (exact local replay, idle zero
  submission, conservative full fallback).
- `draw_ir_composition_damage_spec.spl`: CPU 3/3 PASS; Vulkan 0/2 because the
  backend does not yet expose exact partial-transfer/present receipts.

## Required resolution

Provide a mutation-stable executor boundary: either an Engine2D owner method
that applies a prevalidated clip sequence in one submission, or a result type
that returns and installs the authoritative Engine2D/backend state. Then prove:

1. two disjoint clips update only their pixels;
2. empty damage performs no raster/submit/readback work;
3. invalid, parent-sampling, or real-offscreen batches fail open to one full
   frame;
4. CPU and Vulkan consume the same exact plan without per-rectangle fences;
5. retained two-frame output is pixel-identical to full redraw.

CPU/WM raster ownership is resolved. Vulkan promotion remains blocked on an
honest strided partial-transfer implementation and receipt fields; the current
full-frame host-cache readback must not be reported as device presentation.
