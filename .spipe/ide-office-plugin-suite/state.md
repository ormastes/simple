# Feature: ide-office-plugin-suite

## Raw Request
$sp_dev ide with plugin added verious app supports with plugins(ppt(presentation), excel...) research local and find local impl logic and do not duplicates logics. Ide tui working sanity check and feature check.
ide agent dashboard integration check
ide gui check.
ide md rendering check.
ide ppt rendering, outline view support. improve outline view with css like feature. Change design view of each page with css like change out line text on ppt.
ide tabular data (excel) compatible.
ide db admin interface for embedded db and. simple full db.

## Task Type
feature

## Refined Goal
Integrate the Simple IDE launch surface with the existing plugin, office, markdown rendering, agent dashboard, and database app logic so TUI/GUI modes can expose PPT/slide, spreadsheet/tabular, markdown, and DB admin capabilities without duplicating subsystem implementations.

## Acceptance Criteria
- AC-1: IDE startup advertises and sanity-checks plugin-backed app support for markdown, slides/PPT, sheets/Excel-like tabular data, agent dashboard, and DB admin surfaces using existing app modules.
- AC-2: TUI IDE checks prove the shared editor TUI still starts and renders feature panels including markdown preview and outline surfaces.
- AC-3: GUI IDE checks prove the shared editor GUI launch path remains available and routes through the existing GUI backend.
- AC-4: Markdown rendering support reuses `std.editor.render.md_renderer` and existing editor markdown helpers rather than creating a new renderer.
- AC-5: Slide/PPT support reuses `src/app/office/slides` and includes outline/style metadata that can alter per-slide design and outline text styling.
- AC-6: Tabular spreadsheet support reuses `src/app/office/sheets` data/formula modules and exposes Excel-compatible app capability metadata.
- AC-7: DB admin capability reuses existing embedded/simple DB or portal DB logic and is represented as an IDE app/plugin capability.
- AC-8: Agent dashboard integration check reuses existing dashboard specs or surfaces and is represented as an IDE capability.
- AC-9: Local research documents the existing implementation paths and explicitly identifies duplication boundaries.

## Scope Exclusions
Binary import/export compatibility for proprietary PPTX/XLSX files is not complete unless separately specified; this feature covers IDE capability integration and internal compatible surfaces first.

## Phase
dev-done

## Log
- dev: Created state file with 9 acceptance criteria (type: feature).
- research: Added local research identifying existing IDE, plugin, editor, office, dashboard, and DB implementation paths plus duplication boundaries.
- implement: Added IDE capability registry and `--feature-check` report path for markdown, slides, sheets, agent dashboard, and DB admin metadata.
- implement: Added slide outline CSS-like style helpers that reuse the existing presentation model.
- verify: Focused capability and slide-outline specs pass; direct `bin/simple-interp src/app/ide/main.spl --feature-check` source entrypoint dumps core and is tracked in `doc/08_tracking/bug/ide_feature_check_interpreter_entrypoint_crash_2026-06-01.md`.
- implement: Added focused IDE adapters for spreadsheet compatibility, DB admin, and agent dashboard integration over existing office sheets, editor session DB, portal DB ownership, and editor MCP tools.
- verify: IDE capability system spec now covers six scenarios including sheets formula/range probing, DB admin targets, and agent dashboard MCP tool categories. Direct `--feature-check --tui` and `--feature-check --gui` source-entrypoint checks now exit 0; the earlier crash note is marked resolved.
- verify: `doc/06_spec/system/app/ide/feature/ide_office_plugin_suite_spec.md` includes all six scenarios. The docgen command updated the manual but exited nonzero due to unrelated `src/compiler/10.frontend/flat_ast_bridge_part2.spl` parse error, tracked in `doc/08_tracking/bug/spipe_docgen_flat_ast_bridge_parse_error_2026-06-01.md`.
- implement: Added IDE Markdown rendering and launch sanity adapters over `std.editor.render.md_renderer`, preview pane, block model, and `std.editor.core.launch`.
- verify: IDE capability system spec now covers eight scenarios including Markdown preview rendering and TUI/GUI/SDL launch parsing. `--feature-check --tui` and `--feature-check --gui` both exit 0 and include markdown render and launch sanity summaries.
- implement: Added IDE plugin manifest adapter that serializes capability entries through `app.plugin.registry` and round-trips them through the existing parser.
- implement: Added per-slide CSS-like design metadata helpers in `src/app/office/slides/design.spl`, tied to outline text styling without changing the core slide model.
- verify: IDE capability system spec now covers nine scenarios, including plugin manifest export. Slide outline unit spec now covers outline text styling and per-slide design metadata.
- implement: Added GUI backend sanity adapter over the existing editor GUI Markdown/office renderer and strengthened DB admin probing with existing `simple_db_if` boundary contracts.
- verify: Clean focused checks pass: IDE system spec 10/10, slide outline unit spec 2/2, lint 0 errors, direct `--feature-check --tui` and `--feature-check --gui` both exit 0 and include GUI, plugin manifest, DB admin, sheet, Markdown, and dashboard summaries.
