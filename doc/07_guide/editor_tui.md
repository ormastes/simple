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
  (`src/lib/editor/view/file_tree.spl`).
- **Settings/palette state:** `SettingsViewState`
  (`src/lib/editor/view/settings_view.spl`), `CommandPalette`
  (`src/lib/editor/services/command_palette.spl`).

## Canonical Shared-Library Layout

The editor library follows VS Code-like package names for reusable code:

- `src/lib/editor/buffer/` — text storage, piece table, undo, syntax helpers
- `src/lib/editor/core/` — document/session/keybinding/plugin state
  (`launch.spl` and `path_text.spl` hold reusable app/IDE/MCP helper logic)
- `src/lib/editor/view/` — dock zones, split tree, panels, tabs, breadcrumbs
- `src/lib/editor/render/` — markdown/block/terminal render models
- `src/lib/editor/extensions/` — extension host, manifests, built-ins, and
  reusable extension-root policy (`roots.spl`)
- `src/lib/editor/services/` — LSP, diagnostics, search, wiki, debug, watchers
- `src/lib/editor/unified/` — shared adapters for TUI/VS Code/project surfaces

The extension surface is VS Code-like in behavior, not only in naming:
`src/lib/editor/extensions/host.spl` indexes `extension.sdn` manifests from
configured roots, activates on `onLanguage:*` / `onCommand:*` events, and
registers command, language, and debug-adapter contributions. Root policy stays
in `src/lib/editor/extensions/roots.spl`; app code only injects environment
values. `test/unit/lib/editor/extension_discovery_contract_spec.spl` covers a
real temp-root manifest discovery and activation path.

Do not add duplicate MDSOC-numbered aliases such as `30.view` or
`60.services`. MDSOC+ layering is documented in architecture/design docs; code
paths stay semantic so `src/app/editor`, `src/app/svim`, embedded editor apps,
examples, and the VS Code extension consume one shared editor library.

## Host and SimpleOS Runtime Contract

The editor must remain runnable on both host platforms and SimpleOS:

- `src/lib/editor/` contains runtime-neutral editor/IDE logic only.
- `src/app/editor/tui_main.spl`, `src/app/editor/tui_shell.spl`, and
  `src/lib/editor/70.backend/tui_backend.spl` are the SimpleOS-safe terminal
  path. They may use `std.tui` and shared editor services, but not Tauri,
  Electron, browser/webview, SDL, desktop dialog, or clipboard APIs.
- Host-only presentation and integration belong in adapters:
  `src/app/editor/gui_shell_*`, `src/app/editor/desktop_commands.spl`,
  `src/app/ui.tauri/`, `src/app/ui.browser/`, and related host UI packages.
- Shared GUI rendering is still runtime-neutral: `src/lib/editor/70.backend/gui_backend.spl`
  renders editor and markdown content to pure HTML strings. Web, browser, SDL,
  and Tauri surfaces present those strings through host adapters; they do not
  make Tauri, browser/webview, SDL, or desktop APIs dependencies of the shared
  renderer.
- `test/unit/lib/editor/host_simpleos_surface_contract_spec.spl` enforces this
  boundary with source-level checks and a small runtime render proof.

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

## Current status (2026-05-30)

- **Editor render code: complete** — all editor files compile and link on the
  verified lanes described in
  `doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md`.
- **Frame: renders** via the interpreter proof above and through full native
  TUI loops in both `rust-hosted` and `core-c-bootstrap` lanes, timing out
  normally as expected for an interactive loop.
- **Shared launch parsing/readiness surface: verified** —
  `src/lib/editor/core/launch.spl` is used by `src/app/editor/main.spl`,
  `src/app/editor/tui_main.spl`, `src/app/ide/main.spl`, and
  `examples/ide/simple_ide_launch.spl`. `test/unit/lib/editor/editor_launch_contract_spec.spl`
  runs the IDE and example entrypoints through `bin/simple`; frame-render
  evidence above applies to `src/app/editor/tui_main.spl`, not to the
  readiness-only IDE/example entrypoints.
- **Markdown-first checks:** `test/system/editor_markdown_spec.spl` covers the
  shared markdown block model, renderer, preview pane, table/task/callout
  editing, controller wiring, TUI/GUI preview/status wiring, and property
  diagnostics.

Remaining work should be tracked as focused feature gaps rather than as a
global editor-runtime blocker.

## MCP tool surface & LLM / agent-dashboard integration

The editor also exposes a **55-tool `editor.*` MCP surface** so an agent can
drive it: `editor_mcp_tools()` (registry) and
`editor_mcp_dispatch(session, tool_name, args)` in
`src/app/editor/mcp_tools.spl`. Tools include `editor.open_file`,
`editor.read_buffer`, `editor.edit`, `editor.search`, `editor.diagnostics`,
`editor.goto_definition`, the `editor.lsp_*` family (~21), and the
`editor.wiki_*` family. They are exercised in-process over an `EditSession` in
`test/system/editor_controller_spec.spl`, `editor_md_wiki_index_spec.spl`, and
`editor_gui_spec.spl`.

**Status caveat:** this surface is a *tested library API*, not a live `simple mcp`
endpoint — `editor_mcp_tools()`/`editor_mcp_dispatch()` are **not yet registered
in the MCP server** (`src/app/mcp/main_dispatch.spl` has no `editor.*` routing,
unlike the `assistant_*` tools). Registering it is the missing wire to let agents
drive the editor over MCP.

For how the editor relates to the LLM agent dashboard and assistant session
manager (the `.build/llm_dashboard/assistant/` store, KAIROS three-plane model,
and what is wired vs. contract-only), see
**`doc/07_guide/ide_llm_integration_guide.md`**.
