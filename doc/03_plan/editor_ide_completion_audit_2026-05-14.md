# Editor IDE and Wiki Completion Audit - 2026-05-14

## Scope

Completion audit for `doc/plans/editor_ide_wiki_remaining_goal_2026-05-13.md`
and `doc/03_plan/editor_ide_production_matrix_2026-05-13.md`.

## Matrix Recount

- Command: `rg -n "\| .* \| (PARTIAL|MISSING|BLOCKED) \|" doc/03_plan/editor_ide_production_matrix_2026-05-13.md || true`
- Result: no matching rows.

## Verification Evidence

### 2026-05-30 crash-session recovery revalidation

- Recovered the crashed editor/IDE worktree development session and re-ran the
  broad editor/DAP completion loop after fixing the live DAP `restart` crash and
  replacing source-only pane placeholders with real split-tree operations.
- `failed=0; total=0; for f in test/03_system/editor_*_spec.spl test/03_system/dap_protocol_live_spec.spl; do SIMPLE_LIB=src bin/simple test "$f" --mode=interpreter --fail-fast; done`
  - Result: PASS, 35 files run, 0 failures.
- `SIMPLE_LIB=src bin/simple test test/03_system/dap_protocol_live_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 1 passed.
- `bin/simple test test/01_unit/lib/editor/editor_launch_contract_spec.spl --mode=interpreter --clean`
  - Result: PASS, 5 passed.
- `SIMPLE_LIB=src bin/simple run examples/ide/simple_ide_render.spl`
  - Result: prints `target=pure_simple`, `has_editor_source=true`, and `has_markdown_language=true`.
- `bin/simple run examples/ide/simple_ide_launch.spl`
  - Result: prints `mode=tui`, `files=2`.
- `SIMPLE_LIB=src bin/simple check src/app/dap/simple_dap_main.spl src/lib/editor/view/split_tree.spl src/lib/editor/view/wincmd.spl src/lib/editor/core/session.spl src/app/editor/editor_ctrl_core.spl`
  - Result: PASS.

Recovered implementation state:

- `src/app/dap/simple_dap_main.spl` keeps `restart` inside the session object,
  avoiding the runtime name-resolution crash and preserving stopped-at-entry
  restart evidence in the live DAP smoke.
- `src/lib/editor/view/split_tree.spl` now implements recursive leaf counting,
  pane insertion, resize ratio adjustment, pane swap, and equalize behavior.
- `src/lib/editor/view/wincmd.spl` dispatches Ctrl+W-style focus, split, close,
  only, resize, equalize, and directional swap commands over `EditSession`.
- `src/lib/editor/core/session.spl` exposes `close_active_group()` so close and
  quit window commands keep at least one pane alive.

- `failed=0; total=0; for f in test/03_system/editor_*_spec.spl test/03_system/dap_protocol_live_spec.spl; do ...; done`
  - Result: PASS, 31 files run, 0 failures.
- `src/compiler_rust/target/bootstrap/simple check src/app/dap/simple_dap_main.spl src/app/editor/editor_controller.spl src/lib/editor/services/debug_session.spl test/03_system/dap_protocol_live_spec.spl test/03_system/editor_controller_spec.spl test/03_system/editor_debug_session_spec.spl`
  - Result: PASS, 6 files checked.
- `src/compiler_rust/target/bootstrap/simple check src/app/dap/simple_dap_main.spl src/app/editor/commands.spl src/app/editor/editor_controller.spl src/app/editor/gui_shell.spl src/app/editor/md_dispatch.spl src/app/editor/tui_shell.spl src/lib/editor/view/preview_pane.spl src/lib/editor/services/debug_session.spl src/lib/editor/70.backend/gui_backend.spl test/03_system/dap_protocol_live_spec.spl test/03_system/editor_controller_spec.spl test/03_system/editor_debug_session_spec.spl test/03_system/editor_gui_spec.spl test/03_system/editor_keybinding_spec.spl test/03_system/editor_markdown_spec.spl`
  - Result: PASS, 15 files checked.
- `python3 scripts/smoke/dap_protocol_smoke.py`
  - Result: `STATUS: PASS dap_protocol_smoke`.
- `src/compiler_rust/target/bootstrap/simple test test/03_system/dap_protocol_live_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 1 passed.
- `src/compiler_rust/target/bootstrap/simple test test/03_system/editor_controller_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 92 passed.
- `src/compiler_rust/target/bootstrap/simple test test/03_system/editor_debug_session_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 9 passed.
- `src/compiler_rust/target/bootstrap/simple test test/03_system/editor_keybinding_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 38 passed.
- `src/compiler_rust/target/bootstrap/simple test test/03_system/editor_gui_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 80 passed.
- `src/compiler_rust/target/bootstrap/simple test test/03_system/editor_lsp_transport_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 47 passed.
- `src/compiler_rust/target/bootstrap/simple test test/03_system/editor_palette_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 11 passed.
- `src/compiler_rust/target/bootstrap/simple test test/03_system/editor_session_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 24 passed.
- `src/compiler_rust/target/bootstrap/simple test test/03_system/editor_wal_spec.spl --mode=interpreter --fail-fast`
  - Result: PASS, 23 passed.

## Closed Evidence Areas

- Markdown/wiki parity rows are `PASS`.
- VSCode debug parity rows are `PASS`.
- LSP parity rows are `PASS`.
- DAP source-backed runtime smoke covers launch, conditional breakpoints, hit conditions, stack updates, scoped variables, evaluate, exception stops, restart, terminate, and disconnect.
- Editor controller coverage includes launch configuration selection, compound launch sessions, watch refresh, restart/terminate command routing, and per-session DAP client binding.
- Broad editor/DAP system loop covers all current `test/03_system/editor_*_spec.spl` files plus `dap_protocol_live_spec`.
- Stale source-contract specs were aligned to accessor-based APIs for diagnostics parsing, command palette extension dispatch, session duplicate-tab handling, and session DB fold restore; implementation behavior was already present.

## Status

STATUS: PASS
