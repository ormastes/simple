# app.ui.render.widgets does not re-export render_html_widget/render_html_tree (pre-existing, unrelated to Lane A/C)

**Date:** 2026-07-11 · **Status:** fixed (re-export + LayoutKind rename + stale assertions retargeted)
**Found:** Lane E ("rendering-inside-rendering") baseline run of the existing
widget/chrome specs before writing
`test/02_integration/rendering/browser_chrome_embedded_rendering_spec.spl`.

## Symptom

```
SIMPLE_LIB=src bin/simple test test/unit/app/ui/html_render_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/simple test test/unit/app/ui/widget_button_checkbox_dropdown_spec.spl --mode=interpreter
```

`test/unit/app/ui/html_render_spec.spl`: 0/26 pass, all failures
`semantic: function 'render_html_widget' not found`.

`test/unit/app/ui/widget_button_checkbox_dropdown_spec.spl`: 35/65 pass,
30 failures — same `render_html_widget not found` for every HTML-rendering
`it`, plus a distinct `semantic: unknown variant or method 'Vbox' on enum
LayoutKind` for the three "does not add focused class when X is not focused"
cases specifically (those build a `panel(..., [child])` with a nested-widget
tree, a different code path than the flat single-widget cases).

`test/unit/app/ui/widget_input_textfield_spec.spl` (46/46) is unaffected —
it never imports `render_html_widget`/`render_html_tree`.

## Root cause

Both failing specs import:

```spl
use app.ui.render.widgets.{render_html_widget, render_html_tree}
```

But `src/app/ui.render/widgets.spl` is a thin TUI-only shim:

```spl
# and app.ui.render.html_widgets. This shim keeps only the TUI wrapper surface so
...
use app.ui.render.tui_widgets.{render_tui_tree}
use app.ui.render.colors.{get_theme_color}
```

It never defines or re-exports `render_html_widget`/`render_html_tree`. Those
functions are defined in the sibling module `src/app/ui.render/html_widgets.spl`
(`app.ui.render.html_widgets`). The two specs import from the wrong module
path (or `widgets.spl` is missing a re-export it used to have before the
TUI/HTML split implied by its own comment) — either fix makes both specs
resolve.

The `Vbox` variant failure is a second, separate interpreter symptom
(`LayoutKind.Vbox` is a real variant defined in
`src/lib/common/ui/widget_kind.spl:152/163`) hit only by the nested-panel
construction path in those three "not focused" cases; not investigated
further here since the dominant failure (missing re-export) already accounts
for 47 of the 56 combined failures.

## Confirmed unrelated to Lane A / Lane C

`git status --porcelain` is clean for `test/unit/app/ui/html_render_spec.spl`,
`test/unit/app/ui/widget_button_checkbox_dropdown_spec.spl`,
`src/app/ui.render/widgets.spl`, and `src/app/ui.render/html_widgets.spl` —
none of these files are touched by Lane A's landed draw-IR embedding change
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`) or Lane C's uncommitted
`WmContentFrame`/`wm_gui_content_frame.spl` work, and `render_html_widget`
lives in a completely different renderer (`app.ui.render`, string-HTML widget
tree) than either lane touches (`gc_async_mut.gpu.engine2d` /
`common.ui.window_scene*`). This is a pre-existing bug on `main`, not a
regression from this session's rendering-inside-rendering work.

## Fix applied (2026-07-11, same day)

`src/app/ui.render/widgets.spl` now carries
`export use app.ui.render.html_widgets.{render_html_widget, render_html_tree}`.
Results: `html_render_spec` 0/26 → 21/26; `widget_button_checkbox_dropdown_spec`
35/65 → 57/65.

## Remaining failures (two distinct causes, both pre-existing)

1. **`LayoutKind` merged-graph name collision** (5 + ~several cases:
   `semantic: unknown variant or method 'Vbox' on enum LayoutKind`). The only
   `LayoutKind.Vbox` references live inside `src/lib/common/ui/widget_kind.spl`
   itself (`to_wire`/`from_wire`, :152/:163), so the failure means the
   interpreter resolves `LayoutKind` there to the UNRELATED compiler enum
   `src/compiler/30.types/_TypeLayout/layout_core.spl:119` under merged
   interpreter graphs — same bug class as the documented Logger collision
   (compiler config vs js engine, 2026-07-11). Triggered by the nested-panel
   path (`panel()` → `set_layout("vbox")` → `parse_layout_kind` →
   `LayoutKind.from_wire`). Proper fix: rename the compiler-internal enum
   (e.g. `TypeLayoutKind`, ~10 files under src/compiler/) or fix merged-graph
   symbol resolution; both out of scope for the rendering arc.
2. **Stale assertions**: e.g. "renders input with type checkbox" expects
   `type="checkbox"` but the HTML renderer intentionally emits a div-based
   checkbox (`<div class="widget-checkbox">…<div class="check-box">`). These
   should be retargeted to current renderer output per the #38 stale-spec
   method.

## Residual fixes landed (2026-07-11, later same day)

1. **LayoutKind collision fixed** — compiler-internal enum renamed to
   `TypeLayoutKind` (`src/compiler/30.types/_TypeLayout/layout_core.spl:119`
   + 11 more compiler files + compiler-side test imports). The UI enum in
   `src/lib/common/ui/widget_kind.spl` keeps the `LayoutKind` name. Verified:
   the three "not focused" Vbox cases pass; `sffi_lint_spec` 23/23.
2. **Stale assertions retargeted** — 5 assertions across the two specs
   updated to the real renderer output (div-based checkbox `widget-checkbox`/
   `check-box`; `<option selected>` on default index 0).

Final: `html_render_spec` 26/26; `widget_button_checkbox_dropdown_spec` 65/65.

Noted for separate follow-up (pre-existing, unrelated to this bug):
`struct_reorder_spec`/`bitfield_reorder_spec` assert `case` arms via
`read_text("src/compiler/30.types/type_layout.spl")`, but that file is a
28-line re-export shim with no `case` statements (real arms live in
`layout_core.spl`/`arch_and_verify.spl`) — stale spec, already failing
before the rename. Also `runtime_layout_verification_spec`/
`mir_exported_types_spec` fail on legacy `from hir_definitions import`
module resolution, pre-existing.
