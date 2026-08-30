# Retained DrawIR damage-plan bridge evidence — 2026-08-12

Status: mechanism/correctness PASS; no 8K/80 throughput claim.

## Change

`retained_damage_plan` converts the backend-neutral retained-frame receipt into
the canonical multiscale `DirtyTilePyramid`, starts a fresh epoch, marks every
old/new command bound at every configured scale, and emits the same immutable
`DamageFramePlan` used by CPU and Vulkan consumers. Rejected deltas authorize no
presentation and mark no tiles. DrawIR gains no WebIR, GuiIR, backend, cache, or
tile fields.

## Evidence

- Focused interpreter spec: 4/4 PASS.
- 7680x4320 pure-geometry move: one 256px coarse tile, two 64px CPU tiles, and
  two 32px fine tiles; exact CPU plan is two non-overlapping 64x64 rectangles.
- Settled frame: zero source rectangles, zero dirty tiles, `DAMAGE_PLAN_NONE`.
- Unbounded text: conservative full 7680x4320 plan.
- Malformed/count-changing delta: rejected, zero dirty tiles, no presentation
  authorization.
- O3 optimizer analysis completed; the reported repeated `len()` opportunity
  was removed. Remaining compiler pass opportunities are advisory.

## Honest limitation

This is structural 8K geometry evidence only. It allocates no 8K framebuffer
and does not establish dynamic render p50/p95, RSS, native GPU presentation,
fallback state, or checksum proof. Those remain required for an 8K/80 claim.
