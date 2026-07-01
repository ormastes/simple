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
- Completion audit: `doc/03_plan/editor_ide_completion_audit_2026-05-14.md`.
- Matrix recount: no `PARTIAL`, `MISSING`, or `BLOCKED` rows remain.
- Latest focused editor verification uses `src/compiler_rust/target/bootstrap/simple`.
- Recent completed rows include Markdown live preview/inline editing, Obsidian wiki parity, launch configuration compounds, DAP runtime controls, watch refresh, restart/terminate, multi-session DAP client binding, and LSP polish.

## Remaining Work

| Area | Remaining item | Stop condition |
| --- | --- | --- |
| Markdown visual editor | Complete. | Matrix rows for live preview and inline visual editing are `PASS` with behavior tests for edit, cursor, selection, and preview synchronization. |
| Obsidian wiki | Complete. | Embeds, tables, properties/frontmatter, and callouts rows are `PASS` with TUI and GUI behavior coverage. |
| Debug launch | Complete. | Start debugging shortcut and launch configuration rows are `PASS`, with keybinding, GUI, controller, DAP protocol, launch-config, and compound-launch evidence. |
| Debug runtime controls | Complete. | All debug rows are `PASS`, with DAP protocol tests plus live source-backed runtime behavior tests. |
| LSP polish | Complete. | All LSP rows are `PASS` with controller, TUI/GUI, and async response hydration tests. |
| Production audit | Complete. | No `PARTIAL`, `MISSING`, or `BLOCKED` rows remain; focused editor/debug checks and the broad editor/DAP system loop pass; completion audit documents evidence. |

## Execution Order

1. Completed smaller LSP UI polish rows where existing request/response plumbing already existed.
2. Completed Obsidian/wiki UI parity rows.
3. Completed source-backed DAP runtime controls and editor debug lifecycle parity.
4. Completed final matrix audit and focused editor/debug verification.

## Sync Plan

1. Commit the current editor/wiki matrix and plan updates with a Lore-format
   decision message.
2. Fetch remote refs with `jj git fetch`.
3. Rebase onto `main@origin`.
4. Check tracked file count before and after rebase.
5. Set `main` to the committed revision and push with
   `jj git push --bookmark main`.
