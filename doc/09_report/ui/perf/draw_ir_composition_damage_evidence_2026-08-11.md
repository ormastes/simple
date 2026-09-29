# DrawIR Composition Damage Evidence — 2026-08-11

## Result

PASS for exact retained-surface damage replay on direct CPU and Vulkan DrawIR
compositions. WM production damage selection is connected for same-scene
content, taskbar, and clock changes.

The additive composition executor accepts the canonical `DamageFramePlan` and
resolved image table. For LOCAL plans it:

- validates every half-open rectangle against the persistent surface;
- intersects damage with each embedding clip;
- installs the effective clip in both Engine2D and command replay;
- preserves original batch/command order;
- submits the complete damaged frame once.

NONE performs no command execution, submission, presentation, or readback.
FULL and unsafe LOCAL compositions use the canonical full executor. Unsafe
means translucent embedding, parent/backdrop sampling, required real offscreen
surface, invalid embedding bounds, or invalid damage geometry.

## Verification

```sh
SIMPLE_TIMEOUT_SECONDS=180 \
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json \
bin/simple test \
  test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_composition_damage_spec.spl \
  --mode=interpreter --no-session-daemon
```

Verdict: 4 examples, 0 failures. Whole-buffer oracles prove:

- a full-scene command changes exactly one 2x2 damage rectangle and preserves
  all 60 outside sentinel pixels;
- NONE leaves pixels unchanged and does not submit;
- a translucent embedding reports and performs conservative full fallback;
- Vulkan/lavapipe changes exactly one 2x3 rectangle and preserves all outside
  pixels.

## Honesty Boundary

This proves correctness of the reusable execution seam, not 8K/80 throughput.
Web/GUI owners must still build damage from their canonical revision/property-
tree state. WM now does so through the shared damage pyramid/planner. Vulkan
replay still needs production pairing with exact damaged presentation
transfers. Physical GPU and SimpleOS scanout evidence remain required.
