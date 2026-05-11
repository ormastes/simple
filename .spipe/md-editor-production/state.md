# SStack State: md-editor-production

## User Request
> /dev impll md editor proDuction level

## Phase
8/8 — COMPLETE

## Summary
Wired the existing editor library (~65K LOC, 55 files) into the app layer across all 11 plan phases:

1. MdEditorState on EditorDocument (document.spl)
2. Enter/Tab smart editing intercepts (editor_controller.spl)
3. MdCommandResult glue dispatcher (md_dispatch.spl — NEW)
4. Command palette Ctrl+P (editor_controller.spl, commands.spl)
5. Live preview pane in right dock (tui_shell.spl)
6. Outline panel (tui_shell.spl)
7. Status bar markdown stats (tui_shell.spl, commands.spl)
8. Diagnostics on save (commands.spl)
9. Vim markdown motions ]]/[[ etc (editor_controller.spl)
10. GUI shell wiring (gui_shell.spl)
11. E2E tests — 65/65 pass (editor_markdown_spec.spl)

## Files Modified
- `src/lib/editor/20.core/document.spl` — md_state + cached_md_stats fields
- `src/app/editor/editor_controller.spl` — palette, Enter/Tab intercept, vim motions, preview/outline toggle
- `src/app/editor/md_dispatch.spl` — NEW: MdCommandResult→buffer glue, motion dispatch
- `src/app/editor/tui_shell.spl` — preview/outline rendering, palette overlay, md stats in status bar
- `src/app/editor/commands.spl` — palette/preview/outline commands, diagnostics-on-save, stats recompute
- `src/app/editor/gui_shell.spl` — Ctrl+P, Ctrl+Shift+V/O, preview/outline HTML, md stats
- `test/system/editor_markdown_spec.spl` — 65 structural wiring tests, all passing

## Known Risks
- Cross-layer: document.spl (layer 20) references MdEditorState (layer 50) and md_compute_stats (layer 60). Files parse clean in interpreter. Compiled-mode verification pending bootstrap.
- Editor requires compiled mode (`rt_args` extern) — cannot launch interactively from interpreter.

## Tests
65/65 pass (0 failures)
