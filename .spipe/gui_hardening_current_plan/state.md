# Feature: gui_hardening_current_plan

## Raw Request
$sp_dev (make it sure that all commit on main branch and pushed) complete next plan with spawn agents with pherallel often $sync with gh , check what is done and what is not yet first complete the plan gui_hardening_current_plan...md

## Task Type
todo

## Refined Goal
Complete the current GUI hardening plan by auditing the authoritative plan state, implementing the next open production Chrome parity slice, verifying it with focused GUI hardening gates, and syncing completed commits on main.

## Acceptance Criteria
- AC-1: The current `doc/03_plan/gui_hardening_current_plan_2026-06-01.md` remaining-work state is audited against repo evidence before implementation.
- AC-2: The next production Chrome parity slice reduces or otherwise advances the `site_0_google` production glyph paint/compositing blocker without adding fixture/oracle shortcuts.
- AC-3: Focused checks for the touched browser-engine/wm-compare paths pass or any failures are recorded with the exact failing command and reason.
- AC-4: Dirty changes are reconciled with existing main and `/tmp/simple-js-wasm-*` worktree state without reverting unrelated work.
- AC-5: Completed work is committed on `main`, rebased onto `origin/main` with a file-count guard, and pushed when verification is sufficient.

## Scope Exclusions
Full completion of all remaining GUI hardening lanes in one edit is not assumed; each continuation must preserve the full plan scope and keep uncompleted lanes open.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: todo).
- audit: Current plan has ten open Remaining Work lanes; the smallest next GUI slice is `site_0_google` production glyph paint/compositing.
- audit: VCS is current with `origin/main` at `f77679210c`; no unpushed commits, but main has dirty files and `/tmp/simple-js-wasm-qemu-audit` contains overlapping process-grant tests.
- impl: Tried inline Engine2D text painting for famous-site production rendering after confirming a free helper lost `Engine2D` mutations; the visible text path regressed `site_0_google` from `differentPixels=2717` to `2895`/`3812`, so the renderer experiment was reverted.
- verify: `SIMPLE_LIB=src bin/simple check src/std/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl src/app/wm_compare/site_corpus_compat.spl test/system/wm_compare/famous_site_corpus_spec.spl test/unit/browser_engine/text_painter_spec.spl` passed before the experiment; after revert, `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google` passed at the existing baseline.
- restart-audit: Agent audit found the long-term plan still has open production Chrome parity, 8K, vector-font GPU, JS/WASM, CommonJS/Node, generated GUI WASM, live Electron, QEMU/GTK, and tolerance-audit lanes. The active AC-2 slice remains unproven until a production glyph/compositing change advances `site_0_google` without regressing the 2717-pixel focused baseline.
- restart-audit: Sync audit found `main` and `origin/main` equal at `f77679210c`, but the jj working copy is dirty and there are non-main/unbookmarked jj heads. No push is justified until dirty changes are reconciled and verification is sufficient.
- restart-impl: Rechecked the crashed renderer experiments. Routing the styled corpus block through `simple_web_layout_render_html_pixels` regressed `site_0_google` to `differentPixels=6187`; drawing only overflow Engine2D glyphs regressed to `3300`; drawing smaller glyphs regressed to `3074`/`3056`. All were reverted.
- restart-verify: Restored the passing focused production baseline with `SIMPLE_LIB=src src/compiler_rust/target/release/simple run src/app/wm_compare/site_corpus_compat.spl --only=site_0_google --production-renderer --continue-on-fail --simple-timeout-ms=60000`; `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google` passed at `differentPixels=2717`.
- restart-impl: Advanced AC-2 without a fixture/oracle render shortcut by adding production `text_ink_delta` diagnostics to `site_corpus_compat.spl` and requiring them in `verify_famous_site_production_probe.js`. The report now quantifies the missing glyph/compositing ink: div box has `different_pixels=1612`, `chrome_exact_black_pixels=45`, `simple_background_mismatch_pixels=1612`; overflow text has `different_pixels=1104`, `chrome_exact_black_pixels=22`, `simple_background_mismatch_pixels=1104`.
- restart-verify: `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/app/wm_compare/site_corpus_compat.spl test/system/wm_compare/famous_site_corpus_spec.spl test/unit/browser_engine/text_painter_spec.spl` passed. Regenerated `site_0_google` production report with `--only=site_0_google --production-renderer --continue-on-fail`; `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google` passed with `hasTextInkDelta=true`, `divBoxChromeExactBlackPixels=45`, `overflowChromeExactBlackPixels=22`, and `differentPixels=2717`.
- restart-verify: Required Simple checks for dirty compiler/lib/MCP paths passed: `check src/compiler`, `check src/lib`, `check src/app/mcp`, `check src/app/simple_lsp_mcp`, and `test test/integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`. Focused Rust package tests were attempted for the dirty Rust runtime/compiler set; `cargo test -p simple-runtime` failed 2 tests and `cargo test -p simple-compiler` failed 31 tests, recorded in `build/cargo_test_simple_runtime_pre_sync.out` and `build/cargo_test_simple_compiler_pre_sync.out`.
