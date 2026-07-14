# Legacy Web GUI and WM Shared Font Route Specification

> **Manual draft — pending canonical `spipe-docgen`.** This review copy mirrors
> the executable SSpec while the pure-Simple CLI is unavailable. It is not
> generated-run evidence and does not claim a PASS.

Executable source:
`test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl`

## Scope

This scenario dynamically checks the existing canonical producers:

- `WebRenderBackend.render_html_to_draw_ir` for legacy pure-Simple Web,
- `widget_tree_to_draw_ir_cpu` for GUI widgets, and
- `shared_wm_scene_draw_ir_composition` for WM chrome.

It covers partial REQ-006 and REQ-011. It does not introduce a renderer or
claim native GPU evidence.

## Operator flow

### Render legacy Web GUI and WM text through DrawIR

1. Build one small text composition with each canonical producer.
2. Require exactly one matching text command per producer, then validate its
   `sha256=` identity and the count, numeric values, and width sum of its
   serialized advances.
3. Execute each complete composition through
   `engine2d_draw_ir_adv_composition` on the CPU backend.
4. Require every Draw IR command to render with no skipped command.
5. Re-read the caller-owned producer composition and require identical font
   identity, advances, position, width, and height.
6. Render an isolated black `A` and an otherwise identical empty document on
   white 32×24 CPU surfaces; require non-white ink and a pixel difference from
   the empty baseline, preventing command-count or box-paint-only success.

## Pass boundary

Passing proves structural font-metadata retention in legacy Web, GUI widget,
and WM Draw IR plus submission of each complete composition through the shared
Engine2D CPU route. The isolated witness also proves that this route produces
nonblank CPU text pixels rather than only command metadata. The executor selects
the identity and font size and consumes the serialized advances through the
canonical `FontRenderer`; accepted shaped runs may also carry handle-free glyph
IDs, positions, and logical clusters. This scenario still does not prove native
GPU submission, device readback, or native CPU/GPU pixel parity.

<details>
<summary>Folded executable detail</summary>

The shared checker is `expect_legacy_draw_ir_font_parity`; it runs the real
producer composition and compares the same uniquely selected text command
before and after execution. See the executable source for exact assertions.

</details>
