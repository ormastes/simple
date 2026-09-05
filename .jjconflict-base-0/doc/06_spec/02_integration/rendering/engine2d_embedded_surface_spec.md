# Engine2D Embedded Surface Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 10 | 10 | 0 | 0 |

Status: manually refreshed on 2026-07-13 because TODO 548 blocks the deployed
pure-Simple doc generator. The executable source remains authoritative.

## Scenarios

### Transparent CPU child composition

An independently rendered software child is placed at the requested parent
offset. Painted pixels move with it; untouched transparent pixels preserve the
parent background.

### Embedded bounds and clipping

A batch with a surface ID renders in local coordinates. Commands extending
past the declared child dimensions are clipped before the child is composited.

### Embedded opacity

An opaque red child at `opacity_milli=500` blends over opaque black with the
expected integer alpha result.

### Canonical WM shared Vulkan surface

The real content-aware WM Draw IR producer emits one unfocused window at
`(10,36)`, body size `120x80`, shadow-inclusive scene-clamped surface size
`125x84`, opacity `930`, followed by its resolved `120x52` content IMAGE. The
scenario verifies:

- the first pixel right of the body is shadow-darkened while the pixel after
  the five-pixel shadow remains desktop background;
- body/hit geometry stays `120x80`; the last body pixel focuses the window and
  the first shadow-only pixel dispatches as desktop background;
- translucent shadow metadata and resolved title/close TEXT;
- exact content IMAGE URI and placement;
- child and parent share the same Vulkan or Metal device/session generation;
- creating and shutting the child increments then restores the session count;
- the shared renderer composites a nonzero-alpha child initializer on-device;
- the full CPU and available native GPU frames match exactly; and
- Vulkan or Metal reports device readback, a positive handle, and no skipped work.

Vulkan/Metal absence is an explicit unavailable branch, not a device PASS;
the explicit Metal-on-Vulkan compatibility name is not native Metal. TODO 554
remains open until the focused CPU/device scenario executes with an accepted
pure-Simple runtime.

### Nested embedded output

Pixels from an independently rendered inner child are resolved as an IMAGE in
an outer child and land at the combined offsets.

### Transparent resolved IMAGE

A transparent IMAGE pixel preserves the red parent on the general embedded
path while the opaque pixel is rendered.

### Checked root and named-child Vulkan IMAGE

Preflighted root and named-child IMAGE compositions require exact pixels,
device readback, a positive backend handle, and zero fallback. Opaque IMAGE
commands may use bounded nearest-neighbor scaling; the 2x1-to-3x1 root scenario
must produce `[red, red, green]` on both the CPU oracle and Vulkan device.

1. Scale IMAGE pixels on the Vulkan device with CPU-oracle parity.
2. Blend transparent scaled IMAGE in the full-target named-surface bypass.
3. Scale transparent IMAGE pixels through Vulkan src-over with CPU-oracle parity.

The transparent 2x1-to-3x1 scenario renders inside a named child over
`(20,40,60)` and requires parent output
`[background, (120,70,49), (120,70,49), (20,40,60)]`, device readback, and no fallback.
The regular-composition CPU oracle separately covers the full-target named-
surface bypass and requires `[(120,70,49), (120,70,49), (20,40,60)]`.

After opaque root
initialization, an exact-size opaque IMAGE may cross a bounded named child's
active clip and must retain exact CPU parity and device provenance. A
first-transparent scaled root or partial root initializer, and an opacity-930
initializer, still reject before rendering.

### Checked resolved Vulkan TEXT

Pinned-font TEXT is prepared from canonical glyph material and must match the
CPU frame exactly on Vulkan. Unresolved and off-target TEXT reject before
mutation.

### Mixed invalid fresh-device composition

An opaque IMAGE followed by a translucent later RECT rejects as one unit and
leaves the existing target unchanged.

### Legacy batch without a surface ID

A batch without an embedded surface retains direct translated and clipped
coordinate behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Rendering integration |
| Status | Active; candidate unit run exited 139, no parity PASS |
| Source | `test/02_integration/rendering/engine2d_embedded_surface_spec.spl` |
| Updated | 2026-07-14 (manual) |
| Generator | Manual SPipe refresh; rerun `simple spipe-docgen` after TODO 548 |
