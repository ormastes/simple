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
2d. DONE (landed origin 2ec0229) — **word wired to the substrate**
   (`office/word/html_render.spl`): `render_block_html`/`render_document_html`
   map each `BlockKind` to the resolver theme → styled HTML, against the real
   `attributed_text` DocBlock model (the existing `word/render.spl` targets a
   stale DocBlock API + the broken UI tree). Spec 4/4. All three office surfaces
   — markdown, slides, word — now share ONE CSS substrate.
3. DONE (landed origin 493118d) — **Markdown WYSIWYG view** (`office/md_wysiwyg.spl`):
   `build_wysiwyg_view` pairs each editable source line with its styled-HTML
   preview; `wysiwyg_source_pane`/`wysiwyg_preview_pane` + per-line
   `wysiwyg_update_line` (edit-and-re-render). Pure model→view, no GUI dep — IDE
   TUI+GUI both consume it. Spec `test/01_unit/app/office/md_wysiwyg_spec.spl`
   5/5. Follow-up: wire into the IDE's actual editor surface.
4. DONE (landed origin d0ca1b9) — **PPT renders like MS PPT**:
   `app.office.slides.html_render.render_slide_html` maps each element's role
   (title/subtitle/body, inferred from layout + position) to the resolver's
   slide theme and emits styled HTML. Decoupled into its own file to avoid the
   `common.ui.widget`→`common.ui.style` load chain, which has a pre-existing
   parser bug (`doc/08_tracking/bug/parser_array_index_misread_as_generics_2026-06-14.md`).
   Spec `test/01_unit/app/office/slides/html_render_spec.spl` 4/4. Follow-up:
   wire `slides/render.spl` WidgetNode path + `slides/design.spl` once the
   ui/style parser bug is fixed.
5. TODO — **Excel deeper**: dependency-graph recalc, cell-ref numeric path
   (gated on the f64 blocker), more functions (COUNTA/VLOOKUP/text fns).
6. DONE (landed origin d4323508) — **Plugin split**: `app.office.plugins`
   registers office-word/office-ppt/office-excel as three separate `PluginEntry`
   manifests over the shared md/CSS substrate, via the project's plugin registry
   format (same path the IDE adapter uses). Manifest round-trips + validates.
   Spec `test/01_unit/app/office/plugins_spec.spl` 5/5.
   NOTE: the higher-level office *apps* (`word_app`/`sheets_app`/... exercised by
   `office_suite_spec.spl`) have 13 PRE-EXISTING failures unrelated to these
   slices (stale `word/render.spl` DocBlock API, etc.) — separate cleanup.
7. PARTIAL — **Harden db / SDD-draw / math**:
   - DRAW: DONE (landed origin 0bb2ebae). New `common/drawing/vector_shapes.spl`
     — DrawShape(rect/line/circle/label) on a canvas → well-formed SVG, using
     INTEGER coords to sidestep the f64 bug (the existing Skia SkPoint/SkRect are
     f64). Draw flipped to implemented in the LibreOffice branding (4 live apps).
     Spec 6/6; coords verified via direct run.
   - BASE (db): DONE (landed origin a8e19d0). `office/base_db.spl` — text table
     with insert, `select_where`, `project_column`. Root-caused the blocker: the
     interpreter corrupts `arr.get(n)` for n>=1 (`.get(0)`==ok, `.get(1)` fails
     `==`); fixed by reading cells via for-in iteration (see
     [[feedback_array_get_index_ge1_corruption]]). Spec 6/6 runner-green.
   - MATH: DONE (landed origin a838abeb). `office/math_editor.spl` — renders math
     expressions to MathML (mi/mn/mo) + msup/msqrt helpers. Spec 6/6.
   ALL SIX LibreOffice apps (Writer/Calc/Impress/Draw/Base/Math) now implemented
   and verified (libreoffice spec 6/6, all implemented:true).
8. DONE (landed origin effc1b1) — **Game-tool connect** (`office/game_bridge.spl`):
   declares game↔{calc,draw,db} connection targets; implements Calc-as-game-data
   (`calc_cells_to_game_values`/`calc_row_to_game_tokens` — a game reads level/
   tuning tokens from a spreadsheet by cell ref, verified via direct run:
   "wall floor door"). Draw/Base honestly flagged not-yet-implemented (blocked by
   the same drawing-model/f64 issues as slice 7). Connection-surface spec 2/2.
9. DONE (landed origin 626f970) — **Rename to "LibreOffice"** (minimal/honest):
   `app.office.libreoffice` brands the suite "LibreOffice" and maps components to
   Writer/Calc/Impress/Draw/Base/Math, with an `implemented` flag reporting only
   the 3 substrate-backed apps as live. Emits a LibreOffice-branded plugin
   manifest. Spec `test/01_unit/app/office/libreoffice_spec.spl` 6/6. (Branding
   layer, not a repo-wide symbol sweep — the right minimal interpretation.)

## Log

- 2026-06-14 dev: Opened lane. Measured ground truth (above). Landed slice 1
  (formula hardening) to origin 4fc99a1 with green cycle-termination spec; filed
  the f64-nested-struct toolchain blocker.
- 2026-06-14 dev: Landed slice 2 (office_style_resolver CSS substrate, 3ce12f3,
  spec 8/8) and slice 2b (markdown styled render via the resolver, 1b0da57, spec
  3/3). The CSS-for-md/TUI spine is now end-to-end and verified.
- 2026-06-14 dev: Landed slice 2c (slide theme tags, 0f79db9) and slice 4 (PPT
  styled HTML render via resolver, d0ca1b9, spec 4/4). Refactored ResolvedStyle
  accessors to free functions (style_value/style_has) to avoid a bare-method
  collision with ThemeRegistry.get. Filed pre-existing ui/style.spl parser bug.
- 2026-06-14 dev: Landed slice 2d (word styled HTML render, 2ec0229, spec 4/4)
  and slice 6 (office plugin split, d4323508, spec 5/5). Core suite architecture
  now in place: CSS substrate + all 3 surfaces (md/slides/word) rendering through
  it + word/ppt/excel as separate registered plugins. Remaining: slice 3 (IDE
  WYSIWYG view), 5 (deeper Excel, f64-blocked), 7 (db/draw/math), 8 (game
  connect), 9 (rename to LibreOffice, last/minimal).
