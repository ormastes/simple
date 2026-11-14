# Web renderer form controls vs Chrome 159 — residue after the 2026-11-14 fixes

Oracle: Chrome 159 headless shell 1255, Linux arm64, DSF 1, 900x760. Control
faces: Liberation Sans (`Arial`), DejaVu Sans Mono (`monospace`).

Fixed and pinned by
`test/01_unit/browser_engine/form_control_chrome159_geometry_spec.spl`
(reproducing rows) with `form_control_widget_box_spec.spl` and
`form_control_intrinsic_width_spec.spl` as the generalization specs:

- bitmap-cell advance clamp firing at 9..15 px
  (`simple_web_html_layout_renderer_core.spl`, `metric_scale == 1` without the
  documented `font_size <= 8`) — the AC-12 73 -> 74 regression;
- select width `ceil(label @13.3333px) + 20`, select height `line + 2`;
- text-control widths from the control face's metrics (Liberation Sans
  `8N + 17`, DejaVu Sans Mono `8N + 15`);
- UA control borders / textarea padding / checkbox + radio margins, and the
  cascade memo key that dropped them for the second `<input>` under one parent;
- controls aligned on their inner text baseline; stale `+ 3` on a button line.

## Open

1. **Line strut baseline is 18, Chrome's is 17** for 16 px Liberation Sans on a
   24 px line (`inline_line_strut_baseline_offset`,
   `simple_web_html_layout_renderer_layout_foundation.spl`: half-leading is
   taken against `font_size` 16, Chrome takes it against the face's 17 px
   content area, ascent 14 + descent 3). Effects on forms-media: checkbox and
   radio are 1 px low (y=167/199 vs 165.8/197.8) and the textarea's label is
   54 px vs 55, so everything after the form is 1 px high (details y=364 vs
   364.8, rounded 365). Unblock: derive the content area from the resolved
   face's ascent/descent in the inline text model.
2. **Author `font-size:13px` on a control measures as the UA 13.3333 px.** The
   cascade carries integer px, so the two are indistinguishable in `Style`;
   `<select style="font-size:13px"><option>Alpha` is 57 vs Chrome 56. Unblock:
   a fractional (or flagged) control font size in `Style`.
3. **Control labels are PAINTED at 13 px**, 2.5 % smaller than Chrome's
   13.3333 px (`Exercise controls` 99 px of ink in a 102 px content box).
   Unblock: fractional font sizes in the glyph rasteriser.
4. **Text-control width constants are keyed by face identity** for the two
   Linux faces because there is no OS/2 / `head` table reader; any other face
   keeps the Helvetica/Menlo numbers. `<input>` at an author 16 px (Chrome 215)
   does not fit `(N-1)*round(avg) + round(max)` and is unpinned.
5. **Collapsed inter-element space before `<output>`** is dropped (x=165 vs
   168.9) and the `<output>` run sits 4 px high (y=334 vs 338.8, the button's
   own baseline is not modelled — it stays top-placed). Inline text lane.
6. **Select paint**: the current option label is now laid out and painted, but
   Chrome's `#efefef` menulist background and the drop-down chevron are not;
   checkbox/radio are drawn as outlined boxes instead of Chrome's filled
   accent glyphs; the `<summary>` disclosure triangle paints as a tofu box.
