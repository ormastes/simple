# Detail Design: Simple Web Engine Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Target Branch:** `release/1.0.0`
- **Architecture:** [simple_web_engine_completion.md](../04_architecture/simple_web_engine_completion.md)

---

## Slice 1 Design (`REQ-WEB-001` Float Stacking Order + `REQ-WEB-002` Grid `auto` Track w/ Flex)

### 1.1 `REQ-WEB-001`: CSS 2.2 Appendix E Float Stacking Order

#### Problem Location
1. `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl`:
   - `_html_draw_ir_node_paint_order(nodes, styles)` (`L734-782`) and `_html_draw_ir_append_context_paint_order` (`L640-658`): currently appends every non-context node into `members[parent_context]` in flat document/tree order, so a normal-flow block later in source order paints over an earlier float's box/descendants.
2. `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_raster.spl`:
   - `_paint_passes` Pass 1 (`L1390-1466`): iterates `i = 0..node_count` and paints every `normal_flow` box (both `float_mode == 0` blocks and `float_mode != 0` floats) in flat document order.

#### Design
1. **Shared Float-Subtree Classifier** (no duplicated classification across Draw IR and raster):
   - During the single forward/tree pass (`visit < visit_count`), compute `in_float_subtree[i]: [bool]`:
     - If `_html_draw_ir_opens_context(styles[i])`: `in_float_subtree[i] = false` (a stacking-context root starts its own inner context).
     - Else: `in_float_subtree[i] = (styles[i].float_mode != 0) or (parent >= 0 and not _html_draw_ir_opens_context(styles[parent]) and in_float_subtree[parent])`.
   - Wait — what about `opacity_pct < 100` or `has_relative_paint_root` or `overflow_hidden` clip ancestors?
     - Notice in Draw IR (`_html_draw_ir_node_paint_order`): `parent_context` is already computed per node (`0` for root, `i + 1` for positioned `z >= 0` roots).
     - Inside `context_id`: partition non-context nodes into 3 ordered buckets per context:
       - `members[ctx]` (Layer 3/4): non-float, non-inline-level block boxes (`not in_float_subtree[i]` and `nodes[i].tag != "#text"` and `styles[i].display != "inline"` and `styles[i].display != "inline-block"` and `styles[i].display != "inline-flex"` and `styles[i].display != "inline-grid"` and `styles[i].display != "inline-table"`).
       - `float_members[ctx]` (Layer 5): nodes with `in_float_subtree[i] == true` (both the float box and its in-context descendants, including `#text` inside the float).
       - `inline_members[ctx]` (Layer 7): non-float inline-level / `#text` nodes (`not in_float_subtree[i]` and inline/text).
     -Wait: what if an `opacity_pct < 100` block (with `position: static`) contains both a block background, a float child, and `#text`?
       - In `_simple_web_opacity_roots` (`simple_web_html_layout_renderer.spl:477`), `owner_nodes[cmd_idx]` tracks the owning node, and `_simple_web_layout_compose_retained` groups commands sharing the same `root` (`opacity_pct < 100`). Keeping relative ordering within `members` -> `float_members` -> `inline_members` preserves contiguous group membership if `opacity < 100` does NOT split across different `root`s — wait: if a non-positioned `opacity < 100` block contains a float AND a *subsequent sibling* block outside the `opacity` block overlaps, the `opacity < 100` block ACTUALLY opens a CSS 3 stacking context (`opacity < 1` creates a stacking context per CSS Color 3 §3.2!). Let's verify whether `_html_draw_ir_opens_context` already treats `opacity_pct < 100` as a stacking context or whether `opacity < 1` is handled separately! (We will check `_html_draw_ir_opens_context` callers before editing.)
   - **In Software Raster (`paint_raster.spl`)**:
     - Pass 1 (`normal_flow`) tracks `has_normal_float` boolean in Pass 1a while painting only `normal_flow and not in_float_subtree[i]`.
     - If `has_normal_float` is true, run Pass 1b immediately after Pass 1a (before `flow_outlines` / Passes 2-4 `relative`/`absolute` / Pass 6 `#text`), painting `normal_flow and in_float_subtree[i]`.
     - Zero extra allocation or loop cost on pages with zero floats (`has_normal_float == false`).

### 1.2 `REQ-WEB-002`: CSS Grid `auto` Track w/ Direct or Nested Flex Children
- **Current state:** `grid_auto_track_template_chrome159_spec.spl` passes wrapped `<div><div style="display:flex">` via `flex_item_max_content_width`, while `row_flex_item_auto_intrinsic_w` (`layout_engine.spl:856-857`) still passes `iw` (container `available_w`) to `resolve_horizontal_margin(cst.margin_l, cst.margin_l_pct, iw)` when a grid child *itself* has `display:flex` and a child with `margin-left: 10%` (e.g., `<div style="display:flex"><div style="margin-left:10%;width:40px..."></div></div>`).
- **Fix:** Add explicit `intrinsic_pct_basis: i32` (or pass `0` for percentage margin resolution inside `row_flex_item_auto_intrinsic_w` when called for intrinsic track/flex-base sizing vs definite container sizing), so `%` margins resolve to `0` during max-content contribution per CSS Sizing L3 §5. Verify both wrapped and direct-flex grid `auto` track scenarios against Chrome-159 bounds.

---

## Slice 2 Design (`REQ-WEB-003` + `REQ-WEB-004` Inline `LayoutUnit` & Button Device Precision)
1. **Inline Item `LayoutUnit` (`1/64` px) Ceiling (`layout_foundation.spl:1836-1874`):**
   - Read exact glyph advance sums in font units (`_text_pen_milli` helper) before applying `layout_unit_ceil_milli` once per inline item (including single-edge-space items), removing the `0.6 milli` rounding drift on `<code>button</code>`, `<code>audio</code>`, `<code>a</code>`, and paragraph inline spans.
2. **Flex/Inline/Input Button Device Precision (`layout_engine.spl:4066, 5250, 5350`, `layout_foundation.spl:1004-1042`):**
   - Align `plain_button_item` (`layout_engine.spl:4066`) with `flex_row_button_label_at_edge` (`width_px <= 0 and flex_grow <= 0 and min_width_px <= 0 and min_width_milli <= 0`).
   - Extend `run_pen_origin` & inline button placement for auto-width inline buttons and wrapped/reversed flex button rows.
   - Route `<input type=button|submit|reset>` at `k > 1` through `form_control_label_width_milli_px`, bounded by `FORM_CONTROL_MEASURE_MAX_PX`.
3. **Fractional Follow-ups (`REQ-WEB-004`):**
   - Address `top`/`bottom` vertical-align baseline at `k=4`, `hangs_from_baseline` for `inline-block`, `clear` vs `margin-top`, and post-clamp SVG residual (`web_render_fractional_layout_followups_2026-11-28.sdn`).

---

## Slice 3 Design (`REQ-WEB-005`..`REQ-WEB-008` Interactive `simple browser --open` & Gates)
1. **Interactive State in `main.spl` (`browser_open_window`):**
   - Maintain `BrowserWindowState(url, history: [text], history_idx: i32, scroll_y: i32, max_scroll_y: i32, width: i32, height: i32, commands: [DrawIrCommand])`.
   - Extend `gui_window.spl` (`browser_window_wait` -> `BrowserWindowAction`: `None | Resize(w, h) | Click(x, y) | Wheel(dy) | Key(keycode, scancode) | Close`) while keeping **all rendering calls inside `main.spl`** (`browser_engine_frame_at` / scroll offset compositing).
   - Hit-test clicks against exported `DrawIrCommand.hit_rect` / DOM `<a>` `href` & `<button>` targets; clamp `scroll_y` cleanly on wheel/PageDown/PageUp; bind Backspace/Alt+Left (Back), Alt+Right (Forward), F5/Cmd+R (Reload), Esc/WindowClose (Exit).
2. **Parity Verification (`REQ-WEB-006`, `REQ-WEB-007`, `REQ-WEB-008`):**
   - Verify `check-simple-web-engine2d-js-bitmap-evidence.shs` (`mismatch_count=0`), `check-widget-shells-crossengine-evidence.shs` (`>= 80%`), and complete SSpec manuals under `doc/06_spec/`.
