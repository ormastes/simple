# Panel titles never rendered by the pixel Draw-IR pipeline

- **ID:** widget_draw_ir_panel_title_not_rendered_2026-08-09
- **Status:** FIXED (2026-11-25, fix commit `1f540260dd2` verified)
- **Found by:** computer-use 3D/web/2D showcase sweep, 2026-08-09 — the
  showcase's "Window A" / "Window B" / "Event Probe" panel titles are absent
  from both the 2D PPM and the web HTML capture
- **Area:** `src/lib/common/ui/widget_draw_ir.spl` (+ `src/lib/common/ui/layout.spl`)
- **Severity:** low-medium — cosmetic, but titled panels are indistinguishable
  from plain containers in every pixel host

## Symptom

`builder.panel(id, title, children)` stores a `title` prop; the TUI renderer
draws it on the panel border, but `widget_draw_ir._emit_widget`'s container
branch emits only the background surface rect. The title text reaches no
Draw-IR command, so no pixel host can show it.

## Why not fixed in the 2026-08-09 sweep

Drawing the title inside the panel's top edge needs vertical space the layout
does not reserve: `compute_layout`'s panel branch insets children by exactly
1px (`inner_y = sy + 1`), and that geometry is spec-locked
(`layout_spec.spl` "reserves 1-char border for panel children" builds
`panel("p_outer", "Title", ...)` and asserts the child rect). Emitting the
title without a layout inset would overlap the first child (in the showcase,
the body label starts at the panel top).

## Suggested direction

Reserve a title row in the panel layout branch when `title != ""`
(e.g. `inner_y += TITLE_H`), update the two spec sites that pin the 1px-only
inset, then emit the title text command in `_emit_widget`'s container branch
at `(x + 4, y + 2)`. Alternatively keep layout untouched and render the title
centered ON a thicker drawn top border (Draw-IR-only change, no layout
impact) — visually close to the TUI treatment.

## Triage 2026-09-13
Reconfirmed: pixel Draw-IR pipeline still does not render panel titles per
this record. Needs Draw-IR widget rendering work, not a quick fix. Left
OPEN, no code change attempted.

## Resolution 2026-11-25

**Approach:** fix landed as commit `1f540260dd2` ("fix(ui): render panel
titles with shared pixel client geometry"), following this doc's first
suggested direction with a spec-safe twist: the spec-locked
`compute_layout` keeps its 1px-only panel inset (new `panel_title_height`
parameter defaults to 0, so terminal/TUI geometry is byte-identical), while
a new `compute_pixel_layout` entry point passes
`PIXEL_PANEL_TITLE_HEIGHT = 18` so pixel hosts reserve a title band and
children are laid out below it. `widget_draw_ir._emit_widget`'s container
branch then emits the title as a glyph-bearing text command
(`{rect.id}-title`, same `_default_text_centered` mechanism/font/color
conventions as labels and dialog titles) inside that reserved band; hit
testing (`widget_hit.spl`) uses the same shared geometry so title clicks
stay off the child.

**Before/after evidence** (`_emit_widget` container branch):
- Before (`1f540260dd2^`): only
  `result.push(draw_ir_rect(rect.id, x, y, rect.w, rect.h, theme.surface))`
  — no title command.
- After: probe (`build/`, not committed) of
  `panel("p", "Panel title", [button(...)])` through
  `widget_tree_to_draw_ir_cpu` shows
  `cmd id=p-title kind=text x=4 y=10 text=Panel title` with a valid glyph
  run, and the child button rect starts at y=19 (below the title band).

**Spec results** (self-hosted `bin/simple.exe`, `--mode=interpreter`,
`SIMPLE_LIB=src`, worktree with `assets/fonts` present):
- `test/01_unit/lib/common/ui/widget_draw_ir_panel_title_spec.spl` (the
  regression spec authored for this bug): 5/5 PASS, including
  "rasterizes title glyphs into pixels in the reserved title band".
- `widget_draw_ir_panel_title_bounds_prevention_spec.spl`: 4/4 PASS.
- `widget_draw_ir_glyph_run_spec.spl`: 4/4 PASS.
- `widget_draw_ir_widgets_spec.spl`: 10/10 PASS.
- `test/01_unit/app/ui/layout_spec.spl` (spec-locked 1px panel inset):
  41/41 PASS — locked geometry untouched.

**Verification caveat:** the panel-title and glyph-run specs fail with
`font-runtime-unavailable` (zero glyph runs on *all* text, labels
included) when the pinned font asset
`assets/fonts/google-fonts/ofl/notosansmono/NotoSansMono[wdth,wght].ttf`
is not on disk — e.g. in a sparse-checkout worktree that excludes
`/assets/`. That failure mode is environmental, not a code regression;
re-including `assets/fonts` in the sparse checkout makes all specs above
pass with no code change.
