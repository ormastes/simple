# O2 multiscale damage tiles — 8K structural evidence (2026-08-11)

## Verdict

PASS for backend-neutral damage geometry and classification.

NOT A PERFORMANCE PASS. No p50/p95 frame timing, RSS measurement, Vulkan
submission, framebuffer readback, or 80 fps claim is represented here.

## Evidence identity

| Field | Value |
|---|---|
| Viewport | 7680x4320 |
| Source base | `cc0d7860127` plus working-tree O2 damage patch |
| Execution | Rust bootstrap seed, interpreter correctness only |
| Backend | none; canonical render-opt layer |
| Readback mode | none; pure geometry |
| Fallback state | not applicable |
| p50 / p95 | not measured |
| RSS | not measured |
| Pixel checksum | not applicable; no raster output |
| Focused spec | `test/01_unit/lib/common/ui/render_opt/damage_tiles_spec.spl` |
| Result | 11 passed, 0 failed |
| Manual quality | 80/100, current mirror, 0 blockers |
| Shared plan spec | `damage_plan_spec.spl`: 11 passed, 0 failed |
| DrawIR consumer spec | `draw_ir_damage_plan_spec.spl`: 3 passed, 0 failed |

## Proven structure

- Profile-supplied 256, 64, and 32 pixel grids share one damage owner.
- 8K grid sizes are exact: 30x17, 120x68, and 240x135.
- A bottom-right one-pixel mutation marks one tile per level.
- Ragged bottom tiles contribute clipped areas: 256x224 and 64x32.
- Overlapping damage deduplicates by frame epoch.
- Transform movement retains old and new bounds without becoming full damage.
- `PropertyTrees.damage_*` now feeds every configured scale without clearing or
  stealing source-frame ownership.
- Consumers receive exact clipped flat `[x, y, w, h]` rectangles in O(dirty)
  first-mark order; the 8K bottom-right CPU rect is 64x32 and the coarse rect
  is 256x224.
- The shared CPU/Vulkan frame planner emits deterministic row-major rectangles,
  merges all matching vertical runs, and never widens local damage.
- Area or rectangle-cap fallback emits exactly one full-viewport rectangle with
  an explicit reason and receipt counters.
- The real DrawIR command loop consumes the shared plan as engine clips, keeps
  pixels outside damage unchanged, submits all local rectangles as one batch,
  and executes/submits nothing for an idle retained frame.
- Full-frame classification uses `i64` area math for all 33,177,600 pixels.
- Frame switching clears per-level dirty lengths without scanning every tile.
- Sabotage checks distinguish local damage from force-full redraw and require
  both old and new transform tiles.

## Next consumer gate

Wire the retained WM frame owner to the new DrawIR damage-plan entry point.
Vulkan dispatch clipping is now shared. Native range reads stage exactly the
requested interval rather than copying a prefix. A checked packed-strided read
now packs all rows of one rectangle with one staging allocation, one transfer
command, and one Vulkan region list. Its live nonzero-offset/gapped-row
lavapipe oracle passes, as does the invalid-geometry guard. The canonical
Simple SFFI exposes the operation, and `VulkanBackend.present_damage_plan`
uses it for a seeded retained host mirror while recording exact call, byte,
rectangle, and full-fallback counters. The first frame and invalid/NONE/FULL
plans conservatively use full refresh. The Simple source checker exceeded its
CPU guard without a diagnostic. Focused pinned-lavapipe backend coverage passes
3/3: a seeded 3x2 update transfers exactly 24 bytes with whole-mirror parity,
an idle clean frame transfers zero bytes, and an unseeded mirror records one
full-refresh fallback. Native packed-strided range coverage passes 1/1 plus
1/1 invalid-geometry guards. Native 8K timing remains the next gate;
device-only swapchain presentation is also still separate. A consumer
may claim 8K/80 only with a retained row containing native binary identity,
backend/device, declared damage percentage, p50/p95 <= 12.5 ms, max RSS,
fallback state, nonzero execution counters, and checksum/readback parity.

The native timing harness now exists at
`test/05_perf/graphics_2d/bench_vulkan_8k_retained_damage.spl`. It measures 200
retained 64x64 updates after an 8K seed and emits the required receipt fields.
Current execution is blocked before evidence: forced interpreter exceeded 300
seconds, direct JIT lacked `rt_struct_receiver_valid`, and the entry-closure
native build produced no artifact after more than seven minutes. The blocker
is tracked at
`doc/08_tracking/bug/vulkan_8k_retained_native_evidence_build_blocked_2026-08-11.md`.

An isolated native Vulkan transfer row now narrows the blocker:

| Viewport buffer | Damage | Frames | p50 | p95 | Bytes/frame | Checksum | Result |
|---|---:|---:|---:|---:|---:|---:|---|
| 7680x4320, pinned lavapipe | 64x64 | 200 | 1,087,579 ns | 1,402,461 ns | 16,384 | 1,474,560 | transfer-only PASS |

This row executes the native packed-strided Vulkan primitive with one staging
allocation/command per frame and exact byte parity. It is below the 12.5 ms
budget, but lacks Simple dispatch timing, process RSS, full-frame checksum, and
native Simple binary identity. It therefore does not establish end-to-end
8K/80; it shows that partial device-to-host transfer is no longer the dominant
blocker for this 64x64 damage profile.
