# Editor TUI — components, rendering a frame, and current status

The Simple editor is a terminal (and GUI) code/markdown editor under
`src/app/editor` + `src/lib/editor`. This guide covers what runs today, how to
render an editor frame, and the known blockers.

## Components

- **Entry:** `src/app/editor/tui_main.spl` → `editor_tui_run(session)`
  (`src/app/editor/tui_shell.spl`).
- **Controller:** `EditorController` (`src/app/editor/editor_controller.spl`) —
  key dispatch, mode switching, LSP, debug (DAP), wiki, command palette.
- **Buffer:** `EditorBuffer` (`src/lib/editor/buffer/buffer.spl`, module
  `std.editor.buffer.buffer`) — piece-table text, viewport, folds, cursor,
  semantic tokens. Key API: `from_text(id, content)`, `line_count()`,
  `line_at(n)`, `visible_line_at(row)`, `line_with_fold_marker(row)`.
- **Render panels:** `src/app/editor/tui_shell_panels.spl` — tab bar, file tree,
  editor content (line-number gutter), status bar, command line.
- **File-tree state:** `FileTreeState` / `FileTreeVisibleNode`
  (`src/lib/editor/30.view/file_tree.spl`).
- **Settings/palette state:** `SettingsViewState`
  (`src/lib/editor/30.view/settings_view.spl`), `CommandPalette`
  (`src/lib/editor/60.services/command_palette.spl`).

## Rendering a frame (today)

The full native binary is currently blocked (see Status). To render an editor
frame from the **real `EditorBuffer`** via the interpreter:

1. Write a `.spl` that builds the frame with `print` — not `terminal_write`,
   which the interpreter lacks as the extern `rt_stdout_write`:

   ```simple
   use std.editor.buffer.buffer.*
   use std.editor.common.types.*

   fn main() -> i64:
       val src = "fn main() -> i64:\n    print \"hi\"\n    42\n"
       val buf = EditorBuffer.from_text(EditorBufferId(value: 1), src)
       var frame = "\x1b[2J\x1b[H\x1b[7m  file.spl  \x1b[0m\n"
       var row = 0
       val n = buf.line_count()
       while row < n:
           val num = row + 1
           frame = frame + "  {num} | {buf.line_at(row)}\n"
           row = row + 1
       frame = frame + "\x1b[7m NORMAL  file.spl  {n} lines  \x1b[0m"
       print frame
       0
   ```

2. Narrow `SIMPLE_LIB` to the buffer's small closure (4 files) so the module
   loader does not abort with the 600-file memory-guard (exit 248). Copy into a
   minimal lib tree, preserving module paths:
   - `lib/editor/buffer/buffer.spl`
   - `lib/editor/buffer/piece_table.spl`
   - `lib/editor/00.common/types.spl`

3. Run via the **interpreter** (`bin/simple`, not the bootstrap `seed`):
   ```bash
   SIMPLE_LIB=<minlib> bin/simple run frame.spl
   ```
   The interpreter handles `print` and string concatenation; the bootstrap
   seed's JIT panics on `rt_any_add`.

Output — a drawn editor frame (clear-screen + reverse-video tab bar +
line-numbered content + reverse-video status bar; line count computed by
`EditorBuffer`):

```text
␛[2J␛[H␛[7m  file.spl  ␛[0m
  1 | fn main() -> i64:
  2 |     print "hi"
  3 |     42
  4 | 
␛[7m NORMAL  file.spl  4 lines  ␛[0m
```

## Current status / blockers (2026-05-29)

- **Editor render code: complete** — all editor files compile and link
  (`60 compiled, 0 cached, 0 failed` with `--runtime-bundle rust-hosted`).
- **Frame: renders** via the interpreter path above (the editor's real
  `EditorBuffer`).
- **Full interactive native binary: blocked** by two seed/runtime bugs (not
  editor code):
  - AOT (`core-c-bootstrap`): duplicate `_rt_file_exists` in
    `libsimple_runtime.a`.
  - JIT (`rust-hosted`): `rt_compile_to_native_with_opt` is an interpreter-host
    extern with no C-ABI symbol; the JIT-at-startup cannot resolve it.
  Tracked in `doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md`
  and `editor_jit_run_route_blockers_2026-05-28.md`.
- **Pending feature:** the full markdown-editing subsystem — see
  `doc/08_tracking/feature_request/editor_markdown_editing_subsystem_2026-05-28.md`.

When the seed/runtime bugs land cleanly on `main` (resolving the duplicate
symbol and the interpreter↔JIT extern bridge), a clean bootstrap produces the
full runnable editor — the editor-side code is ready.
