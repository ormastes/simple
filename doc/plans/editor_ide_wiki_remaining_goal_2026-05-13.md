# Editor IDE and Wiki Remaining Goal Plan

Date: 2026-05-13

## Goal

Bring the editor to production-level Obsidian-style Markdown/wiki editing and
VS Code-style IDE support, including debug, shortcut, and LSP workflows. The
source of truth for feature status is
`doc/03_plan/editor_ide_production_matrix_2026-05-13.md`; this plan records the
remaining goal, stop conditions, and sync intent.

## Current Evidence

- Production matrix: `doc/03_plan/editor_ide_production_matrix_2026-05-13.md`.
- Latest GUI/LSP verification: `src/compiler_rust/target/debug/simple check src/app/editor/gui_shell.spl test/system/editor_gui_spec.spl`.
- Latest GUI behavior verification: `src/compiler_rust/target/debug/simple test test/system/editor_gui_spec.spl --mode=interpreter --fail-fast`, 75 passed, 0 failed.
- Recent completed rows in the production matrix include diagnostics, references, and code lens.

## Remaining Work

| Area | Remaining item | Stop condition |
| --- | --- | --- |
| Markdown visual editor | Finish live Markdown preview and inline visual editing parity, including cursor and selection fidelity across rendered blocks. | Matrix rows for live preview and inline visual editing are `PASS` with behavior tests for edit, cursor, selection, and preview synchronization. |
| Obsidian wiki | Finish embeds/transclusion insertion UX, richer TUI table editing, schema-aware frontmatter widgets with selective bulk-edit review, and callout visual preservation/styling. | Embeds, tables, properties/frontmatter, and callouts rows are `PASS` with TUI and GUI behavior coverage. |
| Debug launch | Finish F5 launch-picker handoff, richer GUI picker presentation, launch task/env handoff, compound launch support, and real interpreter runtime debugging. | Start debugging shortcut and launch configuration rows are `PASS`, with process-backed and interpreter-backed smoke evidence. |
| Debug runtime controls | Finish runtime-backed breakpoints, conditional/log/hit breakpoints, stepping, stack frames, variables/scopes, watch refresh, REPL evaluation, exception stop behavior, restart/terminate, and multi-session process binding. | All debug rows are `PASS`, with DAP protocol tests plus live runtime behavior tests. |
| LSP polish | Finish hover delay/decorated-target coverage, quick-fix filtering/grouping, multi-cursor selection UX, rename/format diff UI, non-Markdown document symbols, workspace symbol indexing, semantic token legend/modifier naming, inlay debounce/cancel policy, signature overload navigation, fold visual polish, call hierarchy branch composition, and workspace watch debounce/ignore-glob policy. | All LSP rows are `PASS` with controller, TUI/GUI, and async response hydration tests. |
| Production audit | Recount matrix gaps and run focused checks after each row closure; run full editor verification before claiming completion. | No `PARTIAL`, `MISSING`, or `BLOCKED` rows remain; focused and full editor checks pass; completion audit documents evidence. |

## Execution Order

1. Close the smaller LSP UI polish rows first where existing request/response
   plumbing already exists.
2. Finish Obsidian/wiki UI parity rows that do not depend on runtime debugger
   hooks.
3. Implement interpreter debug hooks and then close the debug runtime rows.
4. Run the final matrix audit, focused editor specs, and broader app/compiler
   checks required by the changed surface.

## Sync Plan

1. Commit the current editor/wiki matrix and plan updates with a Lore-format
   decision message.
2. Fetch remote refs with `jj git fetch`.
3. Rebase onto `main@origin`.
4. Check tracked file count before and after rebase.
5. Set `main` to the committed revision and push with
   `jj git push --bookmark main`.
