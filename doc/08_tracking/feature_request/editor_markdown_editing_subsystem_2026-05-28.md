# Feature Request: Editor markdown-editing subsystem (for full TUI render)

- **Date:** 2026-05-28
- **Area:** `app/editor` + `lib/editor`
- **Status:** open
- **Priority:** medium

## Context

The editor controllers and render panels were written against a markdown-editing
subsystem that was never implemented. With the rich `EditorBuffer` API + LSP
result panel/popups now in place (landed 2026-05-28), the TUI launches into the
alt-screen, but 3 controller files (`editor_ctrl_core`, `editor_ctrl_core2`,
`editor_ctrl_wiki`) and the render panels (`tui_shell_panels.spl`) still fail HIR
type inference because the following do not exist:

- `MdEditorState`, `MdMotionResult`, `MdCommandResult`
- `md_commands_dispatch`, `md_table_*`, `md_callout_*`, `md_vim_*`
- a richer `RenderBlock` / `BlockModel`
- runtime/stdlib gaps: `str.slice`, `discover_extensions`

## Ask

Implement the markdown-editing subsystem so the editor renders and edits markdown
fully. Separable sub-modules:

1. `MdEditorState` + block model (`RenderBlock` / `BlockModel`).
2. Command dispatch (`md_commands_dispatch`, `MdCommandResult`).
3. Motions (`MdMotionResult`) + vim bindings (`md_vim_*`).
4. Tables (`md_table_*`) and callouts (`md_callout_*`).
5. Fill `str.slice` (text method) and `discover_extensions`.

## Interim

A MINIMAL stub set is being added just to compile + draw a basic frame; that is
NOT the full feature. This request tracks the complete subsystem.

## Files

- `src/app/editor/{editor_ctrl_core,editor_ctrl_core2,editor_ctrl_wiki,tui_shell_panels}.spl`
- `src/lib/editor/render/`, `src/lib/editor/30.view/`
