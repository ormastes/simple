# Simple 2D Primitive Lane System-Test Plan

## Scope and verdicts

The lane runs host primitives first, then repeats the same semantic scenarios
through SimpleOS/QEMU. Each row reports `pass`, `unsupported`, `blocked`, or
`fail`; source readiness is never promoted to a live result. The current
compiler-admission and QEMU GPU gates remain authoritative in
`doc/03_plan/sys_test/simpleos_qemu_host_gpu_2d.md`.

## Scenario matrix

| Scenario | Host evidence | QEMU evidence |
|---|---|---|
| Button click and keyboard activation | hit target, one action, pressed/focus Draw IR, duplicate/outside rejection | ordered pointer/key event receipt, changed state epoch, correlated frame |
| Window drag | capture, bounded motion, release/focus-loss cleanup, z-order | guest event receipt, changed WM geometry, exact frame correlation |
| Layout/CSS | computed boxes, invalidation epoch, clip/hit regions, flex/grid/block cases | guest geometry metadata and same Draw IR semantics |
| Scroll | wheel/key/scrollbar route, clamp, nested-chain consumption, clip | guest offset mutation and correlated rerender |
| Font | semantic text/style, resolved font identity, glyph metrics, CPU parity | device font batch/readback/checksum and exact parity |
| Vulkan 2D showcase | animation/drawing/events/font capture, device readback if Vulkan selected | guest/daemon receipt, exact readback, 20 warm p95/RSS |
| Strict DrawIR primitive fixture | clear, opaque rect, straight EDGE, multi-segment linear PATH; dedicated line pipeline; exact explicit device/oracle equality | same bounded fixture through the admitted guest/host Vulkan session |

## Host-first order

1. Web: layout/CSS and browser hit-test/event routing.
2. GUI: widget button, keyboard modifiers, focus, and event pipeline.
3. WM: pointer capture, window drag, clipping, scroll, and rerender.
4. 2D: composition, animation, font, backend selection, readback, and capture.

Use the existing canonical tests:
`test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_hit_test_events_spec.spl`,
`test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl`,
`test/unit/app/ui/widget_button_checkbox_dropdown_spec.spl`,
`test/unit/app/ui/widget_scroll_textarea_spec.spl`,
`test/unit/os/compositor/wm_action_applier_spec.spl`,
`test/unit/os/compositor/layout_manager_spec.spl`,
`test/system/gui/event_processing_spec.spl`,
`test/03_system/ui_showcase/showcase_hosts_spec.spl`, and
`test/03_system/lib/text_layout/vector_font_pipeline_spec.spl`.

Every new or changed SSpec needs real behavior assertions and a generated
manual under `doc/06_spec`; no placeholder pass, screenshot-only assertion, or
source scan can satisfy a scenario.

## SimpleOS/QEMU order

After host rows are green, run the canonical
`scripts/check/check-simpleos-qemu-host-gpu-2d.shs` row for the target ISA.
Require the admitted pure-Simple compiler, exact QEMU argv, event and state
receipts, selected Vulkan backend, fenced device completion, positive device
identity, device-origin pixels, font receipt, zero CPU-oracle mismatches, and
20 post-oracle warm samples with nearest-rank p95 and combined RSS. A missing
compiler, unavailable board capability, TCG-only execution, or missing device
receipt is `blocked`/`unsupported`, never a pass or workaround.

## Current evidence boundary

This plan records the intended acceptance surface. It does not assert that the
primitive host rows or live QEMU Vulkan row currently pass. macOS remains
implementation/test-only under TODO 660; UNO Q remains postponed under the
board TODO and requires physical enumeration plus a SimpleOS-native Adreno
driver lifecycle. Linux/QEMU remains gated by compiler admission and its live
receipt requirements.

## Host container branch ledger

This is an enumerated branch ledger, not a line-coverage percentage claim.
Each row needs the named executable receipt before it is counted as passed.

| Branch family | Positive path | Reject/cancel path | Canonical evidence surface |
|---|---|---|---|
| Click buttons | left down/up accepts one action | unknown button and mismatched/replayed release do not fabricate input | `host_primitive_adapters_spec.spl`, `host_wm_public_bridge_primitives_spec.spl` |
| Drag | press arms, move mutates, release clears capture | release-away/cancel clears without action | `primitive_hosts_system_spec.spl`, `host_compositor_entry_spec.spl` |
| Wheel | positive delta changes the hovered linked scroll owner | zero, negative, and empty-desktop routing remain separately required cases | `host_primitive_adapters_spec.spl`, `host_compositor_entry_spec.spl` |
| Modifiers | Ctrl+Alt survives key-down and key-up | absent/partial modifiers must not be inferred | `host_primitive_adapters_spec.spl`, `host_wm_public_bridge_primitives_spec.spl` |
| Resize | positive host resize updates `size()` before the next composition | non-positive dimensions fail closed at the host boundary | `host_wm_public_bridge_primitives_spec.spl` |
| Wire integrity | ordered numbered event is delivered once | malformed/missing/replayed payload leaves the cursor unchanged | `host_wm_public_bridge_primitives_spec.spl` |
| Layout and font | positive boxes and semantic text/font payload lower to Draw IR | missing layout/text is an explicit test failure | `primitive_hosts_system_spec.spl` |
| Capture | event sequence, frame sequence, raster checksum, and pixel count correlate | disabled export or invalid receipt cannot count as a capture | `host_wm_public_bridge_primitives_spec.spl`, `host_wm_present_no_ppm_spec.spl` |

The first host-container completion report must state the exact run verdict for
each referenced spec. Rows with no executed receipt are `unverified`, not
implicitly covered. The wheel zero/negative and non-positive resize rejection
rows are explicit remaining checks until their focused assertions are present
and executed.

## Ownership

The merge owner is `/root`. Small sidecar lanes are Web/CSS, GUI/button/key,
WM/drag/scroll, and 2D/font/Vulkan/QEMU; each must use disjoint files and
return evidence rather than done claims. Sol is the required higher-model
reviewer for architecture, generated-manual quality, and performance/evidence
boundary before release or completion.
