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
claim native GPU evidence. The hosted color-frame source/unit contract is
separately pinned by `test/03_system/gui/engine2d_gpu_offload_contract_spec.spl`;
neither contract is retained production-run evidence.

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
7. Inspect the shared host Web renderer and require both pixel and readback
   requests to use the HTML-to-DrawIR Engine2D helper instead of the heuristic
   pixel path. Require `ui.browser` to execute one canonical
   `widget_tree_to_draw_ir` composition and reject both its deleted private
   widget command collector and any fabricated runtime-dispatch label. Preserve
   the executor's exact readback source. Inspect
   the production Simple Browser entry and require the same
   helper, exact-byte font registration, and the full
   selected candidate catalog; reject incomplete registration and the private
   software-pixel renderer. Require registered-only mode and exact-byte
   registration to precede the catalog gate, which must precede rendering;
   reject the frame when the shared executor reports a skipped Draw IR command.
   Prefer the readable VFAT path and retain the registry-owned short path only
   for compatibility lookup. Require nonblank pixels and a successful capture
   before the production Browser emits its render marker.
8. Require the pure-Simple FAT32 read owners to retain the bounded 32 MiB
   ceiling needed by the largest pinned 25,125,512-byte selected face, while
   keeping the C compatibility reader's actual 4 MiB bound explicit.

## Pass boundary

Passing proves structural font-metadata retention in legacy Web, GUI widget,
and WM Draw IR plus submission of each complete composition through the shared
Engine2D CPU route. The isolated witness also proves that this route produces
nonblank CPU text pixels rather than only command metadata. The executor selects
the identity and font size and consumes the serialized advances through the
canonical `FontRenderer`; accepted shaped runs may also carry handle-free glyph
IDs, positions, and logical clusters. The source contract also proves that the
Simple Browser registers validated VFS bytes before using that same route; it
does not replace the pending retained QEMU pixel oracle. This scenario still
does not prove native GPU submission, device readback, or native CPU/GPU pixel
parity. The freestanding WM invalid-metrics path now retains canonical legacy
bitmap text rather than rectangle placeholders; it remains compatibility
fallback and does not replace the retained SimpleOS pixel oracle.

<details>
<summary>Folded executable detail</summary>

The shared checker is `expect_legacy_draw_ir_font_parity`; it runs the real
producer composition and compares the same uniquely selected text command
before and after execution. See the executable source for exact assertions.

</details>
