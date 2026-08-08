# Simple 2D Primitive Lane Detail Design

This is the implementation contract for the host-first primitive lane. It is
additive to the existing host-GPU 2D design and intentionally contains no
ad-hoc workaround or alternate renderer.

## Shared state transitions

`InputEvent -> HitResult -> Action -> StateEpoch -> LayoutEpoch ->
DrawIrComposition -> Receipt`. Each transition carries the source generation
and target identity. A rejected event leaves state and epoch unchanged.

### Button click

1. Normalize pointer-down, record hit target and focus.
2. Capture only if the target's action policy permits it.
3. Accept pointer-up only when target, button, and generation match.
4. Emit one action, increment state/layout epoch, and invalidate the affected
   subtree; keyboard Enter/Space routes through the same action.
5. Render semantic pressed/hover/focus state in the next composition.

Outside release, duplicate release, stale generation, and disabled targets are
no-op or explicit rejection paths and must never activate twice.

### Window drag

Window move owns a pointer-capture token, initial pointer/window coordinates,
z-order identity, and generation. Motion applies bounded integer deltas through
the WM layout owner; it does not directly mutate pixels. Release or focus loss
closes the token. Invalid capture, stale window identity, and overflow reject
before layout or Draw IR work.

### Layout, CSS, and scroll

The layout owner resolves style and intrinsic constraints into boxes, clips, and
hit regions. Flex/grid/block and Web CSS adapters map into that owner. A scroll
container has a bounded offset and content/viewport extent; wheel, keyboard,
and scrollbar actions use the same mutation path. Nested scrolling walks the
explicit parent chain once, stopping at the first consumer. `overflow:hidden`
clips but does not imply scrolling. Any geometry change invalidates the minimum
ancestor required by the layout fingerprint and recomposes only after the
epoch is committed.

### Font

Text is emitted with semantic content, style, size, DPI, and resolved font
identity. Engine2D lowers it through `draw_text`; `FontRenderBatch` and atlas
uploads are transient executor material. A device receipt must identify the
font execution target, batch, atlas payload, device readback checksum, and
semantic CPU parity. Missing or stale font material rejects Vulkan promotion.

## Host and QEMU lifecycle

Host adapters create one cached target session, submit bounded immutable
compositions, wait for a fenced terminal completion, read back the logical
ARGB buffer, and shut down only after dependent resources are released. The
QEMU guest uses the existing bounded ivshmem transport and correlated run/frame
IDs. Capability discovery is startup-only; the hot path must not rescan the
tree, reprobe drivers, or spawn a process. Reset, driver/firmware change,
protocol change, or device loss invalidates the session before submission.

The QEMU row is accepted only with the exact guest/daemon argv, selected
backend, positive device identity, event/state receipt, font receipt when text
is present, device-origin readback, zero CPU-oracle mismatches, and 20 warm
samples with nearest-rank p95 plus concurrent RSS. TCG can prove protocol
correctness; it cannot prove native GPU latency.

## Exact implementation/test surfaces

Implementation owners to inspect (no new parallel owners):

- `src/lib/common/ui/screen_host.spl`
- `src/lib/common/ui/input_event.spl`
- `src/lib/common/ui/draw_ir.spl`, `draw_ir_v3.spl`, and widget Draw IR
  producers
- `src/os/compositor/layout_manager.spl`, `flex_layout.spl`,
  `host_gui_event_router.spl`, and `engine2d_wm_frame_executor.spl`
- `src/app/ui_showcase/showcase_core.spl` and `src/app/ui_showcase/hosts/`
- `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`

Existing tests are evidence surfaces, not assumed passes:

- `test/unit/common/ui/input_event_conformance_spec.spl`
- `test/unit/app/ui/widget_button_checkbox_dropdown_spec.spl`
- `test/unit/app/ui/widget_scroll_textarea_spec.spl`
- `test/unit/os/compositor/layout_manager_spec.spl`
- `test/unit/os/compositor/wm_action_applier_spec.spl`
- `test/03_system/ui_showcase/showcase_hosts_spec.spl`
- `test/system/gui/event_processing_spec.spl`
- `test/system/gui/wm_input_qemu_smoke_spec.spl`
- `test/03_system/lib/text_layout/vector_font_pipeline_spec.spl`
- `test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl`

## Sidecar and review contract

Sidecars may inventory one non-overlapping lane: Web layout/CSS, GUI button/
keyboard, WM drag/scroll, or 2D/font/composition. They must return exact source
paths, failing requirement, reproducer, and proposed owner; they may not mark
live QEMU/Vulkan evidence. The merge owner is `/root`; the Sol reviewer must
review architecture boundaries, evidence claims, and performance measurements
before a done mark. Sidecar output is advisory until the primary agent checks
the current source and authoritative test receipt.
