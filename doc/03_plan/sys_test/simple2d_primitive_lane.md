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

## Ownership

The merge owner is `/root`. Small sidecar lanes are Web/CSS, GUI/button/key,
WM/drag/scroll, and 2D/font/Vulkan/QEMU; each must use disjoint files and
return evidence rather than done claims. Sol is the required higher-model
reviewer for architecture, generated-manual quality, and performance/evidence
boundary before release or completion.
