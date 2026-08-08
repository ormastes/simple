# Panel titles never rendered by the pixel Draw-IR pipeline

- **ID:** widget_draw_ir_panel_title_not_rendered_2026-08-09
- **Status:** OPEN
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
