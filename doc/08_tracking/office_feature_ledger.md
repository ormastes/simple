# Office Feature Ledger (phase 0, 2026-08-16)

Scope: `src/app/office/*` apps for the typed-UI-interface plan
(`doc/03_plan/ui/testing/typed_ui_interface_parallel_plan.md`). Classification
is file-level, based on reading the app directories and shared office modules;
"implemented" = code + unit spec exists, "partial" = code exists with gaps or
no live host wiring, "declared-only" = module present but no consumer/host.
Maintained by Agent A; feature agents append rows, never rewrite history.

Shared office modules (all apps): `office_api.spl` (typed command API),
`file_formats.spl` / `odf_ooxml.spl` / `odf_export.spl` / `pptx_export.spl`
(formats), `render_adapter.spl`, `gui_apps.spl` + `launcher.spl` (GUI shell),
`interactive.spl` (TUI shell), `theme.spl`, `erp_bridge.spl`, `plugins.spl`.
GUI launcher wires word/sheets/slides/mail/planner only (`gui_apps.spl`,
`launcher.spl`); notes/publisher/database have NO launcher entry.

## Per-app capability status

### sheets (Calc) — reference vertical
UI hosts: TUI (`calc_tui.spl`, `calc_tui_host.spl`), GUI (`calc_gui_host.spl`),
HTTP (`access_server.spl`, `calc_access_session_host.spl`, snapshot polling —
scheduled for retirement by Agent H), session (`calc_session_host.spl`).
- Implemented: cell model/refs (`cell.spl`, `cell_ref.spl`), formula engine +
  function registry (`formula.spl` — 2 TODOs remain, `function_registry.spl`,
  spec `sheets_function_registry_spec.spl`), grid render (`grid_render.spl`,
  spec `grid_render_spec.spl`), number/cell/conditional format
  (`number_format.spl`, `cell_format.spl`, `cond_format.spl`, spec
  `sheet_gui_cf_spec.spl`), workbook codec (`workbook_codec.spl`),
  access tree + controller (`access_controller.spl`, spec
  `access_controller_spec.spl`).
- Partial: charts (`chart.spl`), pivot (`pivot.spl`), what-if (`what_if.spl`),
  data ops/validation/merge (`data_ops.spl`, `validation.spl`, `merge.spl`),
  math bridge (`math_bridge.spl`).
- Declared-only: coauthoring (`coauthor.spl`), sync (`sync.spl`),
  query (`query.spl`) — no host path exercises them.
- Known defect (arch-doc verified): dual semantic tree + hand JSON in
  `access_controller.spl:129-134,190-282` — deleted in Calc v1 milestone.

### word (Writer)
UI hosts: GUI via launcher (`word_app.spl`, `toolbar.spl`, `sidebar.spl`),
offline HTML (`html_render.spl`). No TUI host, no HTTP host.
- Implemented: edit ops (`edit_ops.spl`, spec `word_edit_ops_spec.spl`),
  tables (`table_ops.spl`, spec `word_table_ops_spec.spl`), TOC (`toc.spl`,
  spec `word_toc_spec.spl`), footnotes (`footnotes.spl`, spec
  `word_footnotes_spec.spl`), HTML render (spec via `md_wysiwyg_render_spec`).
- Partial: mail merge (`mail_merge.spl` + `mail_merge_ui.spl`), page setup
  (`page_setup.spl`), bibliography (`bibliography.spl`), protection
  (`protection.spl`) — modules present, thin host wiring.
- Extension hook covered by `word_extension_spec.spl`.

### slides (Impress)
UI hosts: GUI via launcher (`slides_app.spl`), offline HTML
(`html_render.spl`). No TUI, no HTTP.
- Implemented: deck format (`deck_format.spl`, spec `deck_format_spec.spl`),
  layouts/masters/templates (`layout_registry.spl`, `master.spl`,
  `templates.spl`), shapes (`shapes.spl`), PPTX export (shared
  `pptx_export.spl`, specs `pptx_export_spec.spl`, `pptx_tables_spec.spl`).
- Partial: animations/transitions (`anim_sequence.spl`, `transitions.spl`),
  smartart (`smartart.spl`), chart embed (`chart_embed.spl`), sections,
  outline.
- Known defect (arch-doc verified): element IDs are index-derived
  `el_{kind}_{len}` (`slides_app.spl:155`) — unstable; Agent K moves to
  stable document IDs. Stray editor temp file present:
  `deck_format.spl.tmp.3421194.9f60920de537` (cleanup candidate, not owned
  by this phase).

### mail
UI hosts: GUI via launcher (`mail_app.spl`), offline HTML
(`html_render.spl`, spec `mail_html_render_spec.spl`). No TUI, no HTTP.
- Implemented: message model (`message.spl`), folders (`folders.spl`),
  HTML render.
- Partial: compose (`compose.spl`), rules (`rules.spl`) — demo data
  (`thread_1..5`, `mail_1..5` ids in-source) indicates fixture-driven, no
  real transport.

### notes
UI hosts: none (no launcher entry, no TUI/GUI/HTTP host file). Library-style.
- Implemented: notebook/pages (`notebook.spl`, `page_template.spl`), tags
  (`tags.spl`, spec `notes_tags_spec.spl`), search (`search.spl`); spec
  `notes_spec.spl`.
- Overall: model implemented, UI declared-only (reachable only through
  `office_api.spl`).

### planner
UI hosts: GUI via launcher (`planner_app.spl`), offline HTML
(`html_render.spl`, spec `planner_html_render_spec.spl`). No TUI, no HTTP.
- Implemented: tasks/board/kanban (`task.spl`, `board.spl`, `kanban.spl`),
  list view (`list_view.spl`); launcher GUI spec
  `office_gui_launcher_mail_planner_spec.spl`.
- Partial: calendar view (`calendar_view.spl`), timeline (`timeline.spl`).

### publisher
UI hosts: none (no launcher entry, no host file). Library-style.
- Partial: page layout (`page_layout.spl`), templates (`template.spl`),
  columns/wrap (`columns.spl`, `wrap.spl`), wordart (`wordart.spl`), gallery
  (`gallery.spl`), catalog merge (`catalog_merge.spl`). No dedicated unit
  specs found under `test/01_unit/app/office/` for publisher — treat all as
  partial/declared-only until specs exist.

### database (Base)
UI hosts: none (no launcher entry, no host file). Library-style.
- Implemented: table model (`table.spl`), queries (`query.spl`,
  `param_query.spl`, `action_query.spl`), relations (`relations.spl`);
  spipe fixture `base_db.spl` exercises it.
- Partial: forms (`form.spl`), reports (`report.spl`), QBE (`qbe.spl`),
  io (`io.spl`).

## Cross-app summary

| App | TUI | GUI | HTTP | Model maturity |
|---|---|---|---|---|
| sheets | yes | yes | yes (polling, to retire) | implemented |
| word | no | launcher | no | implemented |
| slides | no | launcher | no | implemented (unstable IDs) |
| mail | no | launcher | no | partial (fixtures) |
| planner | no | launcher | no | partial |
| notes | no | no | no | model-only |
| publisher | no | no | no | declared-only |
| database | no | no | no | model-only |

TODO-marker scan across `src/app/office/**/*.spl`: only
`src/app/office/sheets/formula.spl` (2). Absence of TODOs is NOT evidence of
completeness — most gaps here are missing host wiring, not marked stubs.

## Public widget-ID inventory (used by office tests / access code)

Grep basis: `test/**` + `src/app/office/**` for `surface#widget` strings and
access-node ids (counts = occurrences across test tree, 2026-08-16).

Calc public IDs (the Calc v1 manifest MUST cover exactly these):
- `formula_input` / `main#formula_input` — 9 uses:
  `test/01_unit/app/office/calc_cli_spec.spl`,
  `test/01_unit/app/office/sheets/access_controller_spec.spl`,
  `test/03_system/app/office/feature/office_cli_tui_ui_access_spec.spl`,
  `test/01_unit/app/ui.test_api/action_result_spec.spl`; declared in
  `src/app/office/sheets/access_controller.spl`.
- `confirm_edit` — declared `access_controller.spl`; used by the same specs.
- `sheet_grid` — 2 test uses (same spec set).
- `cell_{ref}` dynamic family — `"cell_"` / `"main#cell_"` prefix matching in
  `access_controller.spl` / `access_server.spl`; becomes typed pattern
  `cell_{CellRef}` per ADR-001 Decision 3.
- Surface: `main` (default), app id `office.calc`, root `spreadsheet`/`root`.

Generic UI-test IDs (not Office; owned by ui_test fixtures — must NOT collide
with app manifests): `main#submit_btn` (43), `popup#ok_btn` (17),
`main#add_task` (13), `main#root`/`s#root`/`a#root`/`z#root` (10/10/8/4),
`main#save` (9), `main#name_input` (8), `main#task_name` (7), `s#w1..w5`,
`popup#stored_ok_btn` (4), `main#task_list` (4), `main#confirm` (4),
`main#confirm`/`tool#name`/`popup#popup_button_0`/`s#child`/`bp#1` (low).

Slides in-source IDs (layout registry, not yet test-addressed): `blank`,
`two_column`, `title_slide`, `title_content`, `section_header`, `text_box`,
`table`, `shape`, `image` (`layout_registry.spl` /
`element_kind_registry.spl`); mail fixtures `thread_1..5`, `mail_1..5`.

Implication for Agent C/D: Calc's public surface is small (3 static ids + 1
pattern + surface `main`) — the compile-failure fixtures (UIE1001/1002/1004)
should be authored against this exact set.
