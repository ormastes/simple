<!-- codex-design -->
# Legacy VS Code Rich Editor UI Sketch

> Status note (2026-05-30): this is a legacy UI sketch for the removed
> standalone VS Code rich-editor package. The current editor/IDE UI source of
> truth is `doc/07_guide/editor_tui.md`, with reusable code in
> `src/lib/editor/` and the product entrypoint in `src/app/ide/main.spl`.
> `examples/10_tooling/ide/**` contains sample integrations only.

**Feature:** legacy `vscode_rich_editor`; current feature is the shared Simple IDE/editor UI
**Date:** 2026-04-12

## Primary Editor Layout

```text
┌──────────────────────────────────────────────────────────────┐
│ Simple IDE / Editor                                         │
├──────────────────────────────────────────────────────────────┤
│ 1  use math                                                 │
│ 2                                                          │
│ 3  val loss = [LOSS]   rendered loss block                  │
│ 4                                                          │
│ 5  val eq = [MATH]    rendered equation at natural height   │
│ 6                                                          │
│ 7  [IMAGE BLOCK]                                           │
│ 8                                                          │
│ 9  val raw = m{ x + y }   <- when cursor enters block      │
└──────────────────────────────────────────────────────────────┘
```

Current UI work is Markdown-first. The same panes/renderers support Markdown
notes, wiki preview, outline, tasks/tables/callouts/attachments, and `.spl`
language editing as one mode of the shared editor.

## Interaction Model

- cursor outside block:
  - rendered widget replaces raw source
- cursor inside block:
  - raw source is revealed for editing
- invalid block:
  - error widget appears in-place without crashing the editor

## Visual Rules

- math widgets use inline or block presentation depending on block type
- images render as block widgets with bounded width
- placeholders and errors use VS Code theme variables
- the editor keeps standard line numbers, selection behavior, and search UX

## Implementation status (2026-05-29)

**Render path: working.** The TUI render code is complete and a real editor
frame has been rendered through the editor's `EditorBuffer` (tab bar +
line-number gutter + content + status bar). Implemented to reach this:
`FileTreeState` / `FileTreeVisibleNode` (`src/lib/editor/view/file_tree.spl`),
`SettingsViewState` (`src/lib/editor/view/settings_view.spl`), plus single-pane no-ops for
the split-border and command-palette renderers (both were written against
undefined APIs — flat-array `SplitNode`, `PaletteState`/`palette_new`).

The full interactive native binary (`editor_tui_run` + controller + key loop)
does not yet run as one executable: AOT links hit a duplicate `rt_file_exists`
in the runtime archive, and the JIT lanes panic on
`rt_compile_to_native_with_opt` (an interpreter-host extern with no C-ABI
symbol). Reproduction of a rendered frame and the current workaround are in
`doc/07_guide/editor_tui.md`; the blockers are tracked in
`doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md`.
