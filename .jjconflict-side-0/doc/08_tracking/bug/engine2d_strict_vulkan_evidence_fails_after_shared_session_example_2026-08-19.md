# BUG: strict Vulkan fresh-device evidence fails after the shared-session WM example in the same process

Status: OPEN (2026-08-19)
Where: `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`
(`_engine2d_draw_ir_execute_strict_vulkan_primitives`, fallback reason
`strict-vulkan-submit-evidence-required`),
`test/02_integration/rendering/engine2d_embedded_surface_spec.spl`

## Symptom

Three examples of `engine2d_embedded_surface_spec.spl` fail:

- "composites a canonical offset translucent WM window on shared Vulkan and Metal sessions"
- "uses the Vulkan device path only for preflighted root and named-child compositions"
- "composites preflighted resolved text through checked Vulkan image blending"

Every `engine2d_draw_ir_adv_fresh_device_composition_with_images` call inside
the full spec run comes back `readback_source=cpu_fallback`,
`backend_handle=0`, with commands skipped (measured by inserting probes after
each result: e.g. WM composition `rend=6 skip=10`, `scaled_blend` `rend=1
skip=2`). The device readback of the WM composition contains ONLY the
antialiased taskbar-clock text pixels (rows 0-89 of the 160x120 canvas all
zero; first nonzero pixel at index 14508), everything else unpainted.

## Evidence that the device path itself is healthy

The exact 3x1 composition from the "preflighted root" example, run in an
isolated spec file through the same `bin/simple test` runner, succeeds:
`readback_source=device_readback backend_handle=1 px=[FF000000, FF008000,
FF000000]` — including the correct a=128 image blend (0xFF008000). It also
succeeds when preceded in the same process by a simple 160x120 Vulkan
create/clear/shutdown session (`backend_handle=2`). Repro scratch specs:
`vk_probe_spec.spl`, `vk_seq_spec.spl` (session scratchpad, 2026-08-19).

So the failure is not "no Vulkan on this host" and not simple sequential
session reuse: it is specific to running after the WM shared-session example
(`create_shared_vulkan_offscreen` / shared Metal session + font/text
rendering) inside one process. Suspects: shared-session generation /
device-identity bookkeeping left behind by the WM example poisoning the
"fresh device" evidence, or font-evidence state
(`draw_ir_font_evidence`) carried across engines.

Note: `Engine2D.create_requested_backend(.., "vulkan")` is also flaky under
`bin/simple run` on this host (intermittent `backend unavailable: vulkan`),
which the spec tolerates via its Err arms; that is a separate environmental
axis from the in-process evidence failure above.

## Repro

```
bin/simple test test/02_integration/rendering/engine2d_embedded_surface_spec.spl
# 10 executed, 7 passed, 3 failed (the three examples above)
```

## Unblock condition

Bisect which sub-state of the WM example (shared vulkan offscreen, shared
metal session, or text/font evidence) flips the strict evidence, then either
reset that state on engine shutdown or make the evidence check ignore
process-level leftovers it should not depend on.
