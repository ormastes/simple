# SStack State: libreoffice-suite

## Status: ACTIVE — opened 2026-06-14

Umbrella program lane. This is a multi-session effort; each slice lands and
verifies independently. Do not treat the whole program as one commit.

## User Request

Improve the IDE; give the md tool a WYSIWYG view beside line-by-line edit; add a
CSS layer for md and TUI to reach MS-Word-level expressiveness; use that CSS to
make the primitive PPT app render like MS PowerPoint; harden the Excel-like
sheet (refs, arithmetic, calc); split word/ppt/excel into separate plugins on
the md module; rename the suite to "LibreOffice"; harden db, SDD/draw, math;
check the game-dev tool and connect it to draw/calc/db. Keep focus on
completing a LibreOffice-like office suite.

## Ground Truth (measured 2026-06-14)

- Office apps already exist under `src/app/office/`:
  `word/` (render,sidebar,toolbar,word_app), `sheets/`
  (cell,cell_ref,formula,render,spreadsheet), `slides/`
  (slide,outline,design,render,templates), plus `planner/`, `mail/`,
  `launcher.spl`, `theme.spl`, `render_adapter.spl`, `mod.spl`.
- Libs: `src/lib/common/markdown/` (full parser; render.spl is MINIMAL —
  `<p>`/heading wrap only, no CSS), `src/lib/common/drawing/`
  (document,selection,vector), `src/lib/common/office/`
  (file_ops,number,search,undo).
- TWO CSS engines exist but are NOT wired to office/md render:
  - `src/lib/blink/css_parser/` — tokenizer, parser (selector + decl blocks),
    selector matcher (type/class/id/compound + specificity). The real engine.
  - `src/lib/common/render_scene/css_types.spl` — CSSDeclaration / CSSValue /
    Selector / CSSRule lighter model.
  - `src/lib/common/ui/glass_css*.spl` — glassmorphism component theming.
- Office render adapters emit `WidgetNode`s with ad-hoc string style TAGS
  (`"paragraph"`, `"heading_N"`, `"bullet_list"`) — not real CSS. The spine gap
  is bridging a CSS engine to these WidgetNode tags so styles cascade for both
  TUI and GUI surfaces.
- Prior agent lanes (CLOSED, finished but NOT "MS-Word level"):
  `m17-css3-completeness`, `md-editor-production`, `editor-ide-platform`;
  `ide-office-plugin-suite` is dev-done and already wired a plugin manifest
  adapter through `app.plugin.registry` and CSS-like slide design helpers
  (`slides/design.spl`).

## Cross-cutting blocker

`doc/08_tracking/bug/interp_f64_nested_struct_payload_zero_2026-06-14.md`:
f64/enum payloads zero out when flowing through deeply nested struct returns on
interpreter/SMF/runner-compiled paths, and the native backend cores on those
paths. This blocks end-to-end NUMERIC verification of the sheet formula engine
(and pre-existing SUM/AVERAGE) and any f64 render geometry. Verify
termination/structural behavior via the runner; verify numerics via direct
`bin/simple run` until the blocker is fixed. Keep slices TEXT/i64-based where
possible so they are runner-verifiable.

## Slices (ordered)

1. DONE (landed origin 4fc99a1) — **Excel formula hardening**: depth-bounded
   cycle detection (circular refs terminate), ROUND half-away-from-zero,
   SQRT/POWER/MOD/INT/TRUNC/PRODUCT/FLOOR/CEILING/SIGN, AND/OR/NOT, `&` concat,
   TRUE/FALSE. Spec: `test/01_unit/app/office/sheets/formula_harden_spec.spl`.
2. DONE (landed origin 3ce12f3) — **CSS substrate bridge** (the spine):
   `std.common.render_scene.office_style_resolver` maps office/markdown element
   tags + utility classes to resolved CSS declarations (text-keyed, Word-level
   default theme) and projects to GUI (CSS text) and TUI (SGR codes). Spec
   `test/01_unit/lib/common/render_scene/office_style_resolver_spec.spl` 8/8
   green. Follow-up: back the cascade with `blink/css_parser` for user CSS.
2b. DONE (landed origin 1b0da57) — **markdown wired to the substrate**:
   `render_markdown_line_styled_html` (in `markdown/render.spl`) emits inline-CSS
   HTML via the resolver — the spine demonstrated end-to-end. Paragraph spec 3/3
   green; heading path verified via direct `bin/simple run` (runner compiled-mode
   i32 interpolation is unreliable — same toolchain fragility as the f64 bug).
3. TODO — **Markdown WYSIWYG view in IDE**: styled preview beside line edit,
   using slices 2/2b. Reuse `std.editor.render.md_renderer` (AC-4 of
   ide-office-plugin-suite) — do not write a new renderer.
4. TODO — **PPT renders like MS PPT**: apply slice-2 CSS to `slides/render` +
   `slides/design` per-slide design and outline styling.
5. TODO — **Excel deeper**: dependency-graph recalc, cell-ref numeric path
   (gated on the f64 blocker), more functions (COUNTA/VLOOKUP/text fns).
6. TODO — **Plugin split**: word/ppt/excel as separate plugins on the md module
   via `app.plugin.registry` (reuse ide-office-plugin-suite manifest adapter).
7. TODO — **Harden db / SDD-draw / math**: `simple_db`, `common/drawing`,
   math; connect draw to the CSS/render substrate.
8. TODO — **Game-tool migrate + connect**: `examples/11_advanced/game2d`
   connect to draw/calc/db.
9. TODO (LAST, MINIMAL) — **Rename to "LibreOffice"**: user-facing app/branding
   names only; NOT a repo-wide symbol sweep (high-conflict, low-value churn in
   this parallel-force-push repo).

## Log

- 2026-06-14 dev: Opened lane. Measured ground truth (above). Landed slice 1
  (formula hardening) to origin 4fc99a1 with green cycle-termination spec; filed
  the f64-nested-struct toolchain blocker.
- 2026-06-14 dev: Landed slice 2 (office_style_resolver CSS substrate, 3ce12f3,
  spec 8/8) and slice 2b (markdown styled render via the resolver, 1b0da57, spec
  3/3). The CSS-for-md/TUI spine is now end-to-end and verified. Next: slice 3
  (IDE WYSIWYG view) and slice 4 (PPT render via resolver).
