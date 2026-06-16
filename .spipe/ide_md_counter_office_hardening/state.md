# Feature: ide-md-counter-office-hardening

## Raw Request

`$sp_dev harden ide md drawing and editing, harden counter libre office app. make them production level. apply next optimizations gui_web_2d_render_optimization_2026-06-16.md do with spark and normal llm in pherallel spawn agents. review spark job after done`

## Task Type

feature

## Refined Goal

Make IDE markdown drawing/editing and the counter/LibreOffice-style office app production-ready by adding fail-closed behavior, real SPipe evidence, and the next retained/visibility/cache optimizations from `doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md`.

## Acceptance Criteria

- AC-1: IDE markdown rendering/drawing has deterministic Draw IR or equivalent structured evidence for headings, lists, code blocks, diagrams, and edits, with no screenshot-only or placeholder assertions.
- AC-2: IDE markdown editing preserves document text, cursor/selection intent, and markdown structure across insert/delete/format actions, with bounded handling for malformed or oversized markdown.
- AC-3: Counter/LibreOffice-style office entrypoints fail closed on invalid commands/data, expose deterministic state transitions, and have production-level evidence for app launch, counter interaction, and document/sheet/slide surface routing.
- AC-4: The first optimization slice from `gui_web_2d_render_optimization_2026-06-16.md` is applied where it is safe: retained/visibility/cache metadata must skip invisible or unchanged work without changing visible output.
- AC-5: Performance-sensitive touched `.spl` files have a baseline, optimizer run, and after-check evidence, or a tracked blocker explaining why the optimization app cannot run.
- AC-6: Normal and Spark agents run in parallel with disjoint ownership; Spark output is reviewed before integration.
- AC-7: Generated/manual SPipe docs are refreshed for changed executable specs, and `find doc/06_spec -name '*_spec.spl' | wc -l` remains `0`.

## Scope Exclusions

- Do not claim full GPU speedup without hardware readback/counter evidence.
- Do not rewrite IDE or office surfaces in C/Rust.
- Do not absorb unrelated jj/bookmark conflict work into this feature lane.

## Phase

dev-done

## Log

- dev: Created state file with 7 acceptance criteria (type: feature).
- integration/evidence: Normal-model lane is planning/evidence/docs only; do not edit Spark-owned implementation files, sync/rebase/push, or resolve unrelated main bookmark conflicts.
- integration/evidence: Existing high-signal specs include `test/03_system/gui/editor_markdown_spec.spl`, `test/03_system/gui/editor_markdown_document_decor_spec.spl`, `test/03_system/gui/editor_markdown_office_layout_spec.spl`, `test/01_unit/lib/editor/md_editing_spec.spl`, `test/01_unit/lib/editor/render/md_renderer_hardening_spec.spl`, `test/01_unit/lib/editor/render/md_draw_ir_spec.spl`, `test/01_unit/app/office/office_suite_spec.spl`, `test/01_unit/app/office/libreoffice_spec.spl`, `test/01_unit/app/office/md_wysiwyg_spec.spl`, `test/01_unit/app/office/md_wysiwyg_render_spec.spl`, `test/01_unit/app/ui/web_render_cache_spec.spl`, `test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl`, and `test/05_perf/web_render_chrome/web_paint_cache_spec.spl`.
- integration/evidence: Generated/manual docs already exist for the main GUI markdown system specs, `office_suite_spec`, `slide_outline_spec`, `web_render_cache_spec`, `window_scene_draw_ir_spec`, and `web_paint_cache_spec`; missing/manual-doc follow-up is needed for real office unit specs such as `base_db_spec`, `game_bridge_spec`, `libreoffice_spec`, `math_editor_spec`, `md_wysiwyg_spec`, `md_wysiwyg_render_spec`, `plugins_spec`, `sheets/formula_harden_spec`, and `slides/html_render_spec`. `.spipe_matchers_*` and runner/helper files should be reviewed before docgen because they may not be intended scenario manuals.
- integration/evidence: Focused verification commands for integration are `sh scripts/setup/install-spipe-dev-command.shs --check`, `find doc/06_spec -name '*_spec.spl' | wc -l`, `bin/simple test test/03_system/gui/editor_markdown_spec.spl`, `bin/simple test test/03_system/gui/editor_markdown_document_decor_spec.spl`, `bin/simple test test/03_system/gui/editor_markdown_office_layout_spec.spl`, `bin/simple test test/01_unit/lib/editor/md_editing_spec.spl`, `bin/simple test test/01_unit/lib/editor/render/md_renderer_hardening_spec.spl`, `bin/simple test test/01_unit/lib/editor/render/md_draw_ir_spec.spl`, `bin/simple test test/01_unit/app/office/office_suite_spec.spl`, `bin/simple test test/01_unit/app/office/libreoffice_spec.spl`, `bin/simple test test/01_unit/app/office/md_wysiwyg_spec.spl`, `bin/simple test test/01_unit/app/office/md_wysiwyg_render_spec.spl`, `bin/simple test test/01_unit/app/ui/web_render_cache_spec.spl`, `bin/simple test test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl`, `bin/simple test test/05_perf/web_render_chrome/web_paint_cache_spec.spl`, `bin/simple test test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl`, and `sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs`.
- integration/evidence: Optimizer baseline/after-check candidates are touched `.spl` files in `src/app/ide/markdown_render.spl`, `src/lib/editor/render/md_draw_ir.spl`, `src/lib/editor/view/markdown_state.spl`, `src/lib/editor/view/md_editing.spl`, `src/lib/editor/extensions/builtin/md_edit_assist.spl`, `src/app/office/libreoffice.spl`, `src/app/office/launcher.spl`, `src/app/office/base_db.spl`, `src/lib/common/ui/draw_ir.spl`, `src/lib/common/ui/window_scene_draw_ir.spl`, `src/lib/common/ui/window_scene.spl`, `src/lib/common/ui/web_render_api.spl`, and `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`; run `bin/simple run src/app/optimize/main.spl <file> --full --level=O3` only for files actually changed by Spark/normal implementation workers.
- integration/evidence: Spark job review gate: inspect Spark-changed files, confirm disjoint ownership, require AC-1..AC-7 mapping, reject screenshot-only/placeholder rendering evidence, reject new boolean-wrapper assertions, require baseline + optimizer + after-check evidence for performance-sensitive changed `.spl` files, refresh generated manuals for changed executable specs, and keep `doc/06_spec` executable-spec count at `0`.
- integration/evidence: Normal explorer addenda: include `SIMPLE_LIB=src` for focused test commands, add `test/02_integration/app/ide/ide_feature_check_integration_spec.spl`, `test/03_system/app/ide/feature/ide_office_plugin_suite_spec.spl`, `test/02_integration/rendering/simple_web_layout_child_index_spec.spl`, `test/02_integration/rendering/simple_web_titlebar_nowrap_spec.spl`, `test/01_unit/lib/common/ui/window_scene_draw_ir_layer_order_spec.spl`, `test/01_unit/app/ui/browser_backend_runtime_queue_spec.spl`, `sh scripts/check/check-node-web-render-bitmap-evidence.shs`, and `sh scripts/check/check-bun-web-render-bitmap-evidence.shs` to the verification set when implementation touches those surfaces.
- integration/evidence: Normal explorer optimizer addenda: also consider `src/lib/editor/render/md_renderer.spl`, `src/lib/editor/render/block_model.spl`, `src/app/office/md_wysiwyg.spl`, `src/app/ui.web/render_cache.spl`, `src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl`, and `src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl` if those files are actually changed; rerun the exact same baseline block after slice-1 visibility/containment/cache work.
- integration/evidence: Spark explorer addenda: include existing IDE markdown specs `test/03_system/gui/editor_md_language_spec.spl`, `test/03_system/gui/editor_md_lsp_code_action_spec.spl`, and `test/03_system/gui/editor_md_wiki_index_spec.spl`; Draw IR/UI specs `test/03_system/app/ui_test_api/feature/draw_ir_protocol_evidence_spec.spl`, `test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl`, and `test/03_system/app/ui/feature/shared_wm_renderer_unification_spec.spl`; and Simple Web/2D specs `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl`, `test/03_system/gui/gui_entry_engine2d_virtio_spec.spl`, `test/03_system/gui/layered_simple_gui_web_engine2d_bitmap_evidence_spec.spl`, `test/03_system/gui/widget_rendering_spec.spl`, `test/03_system/gui/headless_rendering_spec.spl`, `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`, and `test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl` when those surfaces are touched.
- integration/evidence: Spark explorer weak-evidence risks to review before claiming production level: `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl` contains `expect(true).to_equal(true)`, and mirrored docs `doc/06_spec/perf/graphics_2d/metal_readback_proof_spec.md` plus `doc/06_spec/test/05_perf/graphics_2d/metal_readback_proof_spec.md` contain the same weak pattern; these are not necessarily lane-owned edits, so record or route separately if untouched by Spark.
