<!-- codex-design -->
# Simple 2D Primitive Lane Architecture

Status: design and evidence map, 2026-08-08. This document defines the
host-first primitive lane for buttons, window dragging, layout/CSS, scrolling,
and fonts across Web, GUI, WM, and 2D. It does not claim a live QEMU or GPU
pass.

## Decision

Keep one semantic interaction and layout pipeline:

```text
host input -> common event normalization -> hit/layout owner
  -> semantic state mutation -> DrawIrComposition
  -> Engine2D backend lane -> host presentation/readback
```

Web, GUI, WM, and 2D are producers or adapters of the same semantic result.
They must not grow per-surface button, drag, scroll, font-atlas, or Vulkan
implementations. `DrawIrComposition` is the boundary before rendering;
`FontRenderer`/transient `FontRenderBatch` remains the font material owner.
SimpleOS/QEMU consumes the already-formed composition through the existing
`SimpleOsHostGpuSession`/ivshmem capsule and does not add a second event router
or renderer.

## Layers and ownership

| Layer | Canonical owners | Public obligation |
|---|---|---|
| Input | `src/lib/common/ui/input_event.spl`, `src/os/gui/input_event.spl` | Normalize pointer, wheel, key, and Ctrl/Alt/Shift modifiers with stable ordering. |
| Semantics | widget/event and WM action owners | Hit-test, click activation, pointer capture, focus, drag, and scroll state. |
| Layout | `src/os/compositor/layout_manager.spl`, `src/os/compositor/flex_layout.spl`, Web layout owners | Resolve CSS/layout boxes and scroll clips before paint; reject invalid geometry. |
| Composition | `src/lib/common/ui/draw_ir*.spl`, widget Draw IR producer | Emit one immutable `DrawIrComposition`; preserve semantic text/style. |
| Execution | `src/lib/gc_async_mut/gpu/engine2d/`, `src/os/compositor/engine2d_wm_frame_executor.spl` | Select Vulkan only when device completion/readback evidence is complete; otherwise explicit CPU/SIMD fallback. |
| Targets | host adapters and `SimpleOsHostGpuSession` | Own device lifecycle, bounded resources, fence, readback, and provenance. |

### MDSOC visibility rule

Common input, layout facts, composition schema, and receipt validators are
public to the next layer. Web, GUI, WM, and target adapters remain tree-private
siblings. A sibling may consume only a common contract or explicit facade; it
may not import another surface's private hit-test, CSS, font cache, or backend
state.

| Raw layer | Common input | Common layout | DrawIrComposition | Font material | Target receipt |
|---|---|---|---|---|---|
| Web | public | public Web-layout facade | public producer | transient renderer facade | validator only |
| GUI | public | public widget/layout facade | public producer | transient renderer facade | validator only |
| WM | public | public window/layout facade | public producer | transient renderer facade | validator only |
| 2D | public | public scene/layout facade | public producer | transient renderer facade | executor consumer |
| SimpleOS/QEMU | guest event facade | guest geometry metadata | transport consumer | host renderer owner | capsule owner |

## Primitive invariants

- A click requires a matching press/release target, active focus, and exactly
  one semantic activation; keyboard activation follows the same action owner.
- A drag captures the pointer after the accepted press, updates one window
  through motion, and releases capture deterministically; no surface-local
  polling loop may synthesize movement.
- Layout computes boxes once per invalidation epoch. Overflow clipping and
  scrolling are distinct; scroll offsets are clamped and included in hit-test
  and Draw IR invalidation.
- Text remains semantic in Draw IR. Glyph atlas/cache material is transient
  Engine2D state, never a Draw IR field or a second font path.
- Vulkan promotion requires selected backend `vulkan`, fenced device execution,
  positive device identity/handle, device-origin readback, exact CPU oracle
  parity, and complete font receipt where text is present. A screenshot,
  scanout, CPU mirror, or QEMU flag is not promotion evidence.

## Platform boundaries and current state

Host implementation and contract tests may run in the container. SimpleOS
execution requires the canonical QEMU wrapper and an admitted pure-Simple
compiler; source checks, phase-2 diagnostics, and TCG correctness do not prove
the production Vulkan row. macOS is implementation/test-only and remains a
TODO-gated emulation row. UNO Q is postponed until board enumeration and the
SimpleOS Adreno lifecycle (firmware, MMU/cache, queue, fence, readback, display)
exist. These deferrals are explicit classifications, not fallback passes.

### QRB2210 physical composition boundary

The UNO Q lane now has a typed next-layer boundary in
`os.port.qrb2210_native_2d_ports`: display/present, normalized `HostInputEvent`,
PCM audio, Vulkan submit, fence completion, and device-origin readback are six
separate physical provider ports. `qrb2210_native_2d_composition_root` is the
only board admission point and names the route
`shared-wm-drawir-engine2d-qualcomm-vulkan`. It rejects any Engine2D backend
other than `qualcomm` and any GPU provider not identifying Qualcomm Vulkan
vendor `0x5143`. The port definitions do not implement hardware or generate
receipts.

Every one of those capabilities still returns canonical `port-unavailable`.
Consequently the QRB2210 entry fails before binding the composition root, and
no source contract, Debian run, QEMU adapter, or caller-supplied object can
promote the physical-board row.

## Migration sequence

1. Complete and verify each primitive on the Linux host surface.
2. Exercise the same contracts through GUI, WM, Web, and 2D adapters with no
   semantic duplication.
3. Run the bounded SimpleOS/QEMU lifecycle and retain event, font, readback,
   and performance receipts.
4. Promote Vulkan only after device-origin evidence; record blocked rows with
   their exact reason and resume command.
