# DrawIR Vulkan damage-present route — 2026-08-12

Status: production route and focused contract PASS; no 8K/80 claim.

## Result

The retained DrawIR composition path no longer sends a valid local
`DamageFramePlan` through generic `Engine2D.present()`, which forced Vulkan to
download the full framebuffer. `Engine2D.present_damage_plan()` now dispatches
that plan to `VulkanBackend.present_damage_plan()`, whose native strided reads
transfer only the planned rectangles into the seeded host mirror.

Idle plans are no-ops. Invalid/full plans and conservative offscreen or
parent-sampling fallbacks retain the full-present path. CPU and bare-metal
backends retain existing presentation behavior.

## Evidence

- Focused source/runtime contract: 3/3 PASS with the Engine2D facade compiled.
- Existing composition-damage baseline exceeded the default 60-second
  interpreter guard before a verdict; it was not reported as a pass.
- O3 analysis completed for both touched production modules. Remaining findings
  are broad pre-existing whole-file opportunities, not evidence of this route's
  throughput.

## Remaining gate

The route removes a known full-frame readback from local-damage presentation,
but 7680x4320 dynamic p50/p95, RSS, fallback, native-device identity, exact
transfer-byte receipt, and checksum evidence remain required before claiming
8K at 80 fps.
