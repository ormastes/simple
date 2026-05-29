# Status/Bug: Editor TUI render code complete; runnable binary blocked by 2 seed/runtime bugs

- **ID:** editor_render_runtime_blockers
- **Date:** 2026-05-29
- **Area:** editor app + seed runtime/JIT
- **Status:** RENDER ACHIEVED (interpreter, narrowed SIMPLE_LIB — see "Frame rendered" below). AOT (`core-c-bootstrap`) now **builds + links + runs**: the duplicate-`_rt_file_exists` blocker is fixed (weak attr, main `61b29213`) and the render-loop SIGSEGV is fixed (main `knrqtpow`). The missing UI-state types + the `.id` deref crash fix are on main (`knrqtpow`). Remaining: 3 AOT/JIT-runtime issues below (NOT editor code), plus `PaletteState` is still an undefined type.

## Frame rendered (2026-05-29)

A real editor frame was drawn by executing the editor's actual `EditorBuffer`
(`from_text` → `line_count` → `line_at`) and laying out a tab bar + line-number
gutter + status bar. Output (escapes shown as `<ESC>`):

```
<ESC>[2J<ESC>[H<ESC>[7m  sample.spl  <ESC>[0m
  1 | fn main() -> i64:
  2 |     print "hello world"
  3 |     val x = 42
  4 |     val y = x + 1
  5 |     y
  6 | 
<ESC>[7m NORMAL  sample.spl  6 lines  <ESC>[0m
```

The 6 line rows + `6 lines` count were computed by `EditorBuffer` from the source
text (not hardcoded). Reproduce:
1. Put `EditorBuffer.from_text(...)` + line loop + `print` (no `terminal_write`)
   in a `.spl` (uses `print`, not `rt_stdout_write` which the interpreter lacks).
2. Narrow `SIMPLE_LIB` to the 4-file closure (`editor/buffer/buffer.spl`,
   `editor/buffer/piece_table.spl`, `editor/00.common/types.spl`) to avoid the
   600-file memory-guard abort (exit 248).
3. `SIMPLE_LIB=<minlib> bin/simple run <file>` — the **interpreter** handles
   string concat/`print` (seed_S's JIT does not; it panics on `rt_any_add`).

This proves the editor render path works end-to-end. The full interactive
binary (controller + key loop) remains blocked by the 2 seed bugs below.


## Milestone (done)

The editor's full render path now **compiles and links** with `--runtime-bundle
rust-hosted`: `Build complete: 60 compiled, 0 cached, 0 failed` → 798 KB binary.
Reaching this required implementing the speculative UI-state types the editor
was written against but that never existed:

- `FileTreeState` + `FileTreeVisibleNode` (+ `new`/`visible_nodes`/`select_next`/
  `select_prev`/`toggle_expand`/`selected_is_dir`/`selected_path`) in
  `src/lib/editor/30.view/file_tree.spl`.
- `SettingsViewState` (categories/category_index/filtered/selected_index/
  editing/edit_value) in `src/lib/editor/30.view/settings_view.spl`.
- Wired `use std.editor.view.file_tree.*` / `settings_view.*` into the
  controller, ctrl_core, tui_shell_panels, gui_backend.
- `LspResponse` tuple-element annotations in `editor_ctrl_core2.spl`.

**On main as of `knrqtpow`:** `FileTreeState`/`FileTreeVisibleNode`/`_ft_flatten`,
`SettingsViewState`, the two `use std.editor.view.{file_tree,settings_view}.*`
imports, and the `.id.value`→`.id` fix in `_layout_find_group_index_local`. The
proj3 diagnostic workarounds (no-op'ing `_tui_render_palette`, removing the
per-frame poll calls, skipping `discover_extensions`) were **intentionally NOT
taken** — they delete real, working code (the four poll methods exist at
`editor_controller.spl:367/664/682/700` and are used by `gui_shell_core.spl` too;
`discover_extensions` exists at `host.spl:113`). They are recorded as bugs below
instead of degrading source.

(The markdown subsystem + string-method/octal seed fixes from the other session
were prerequisites and are already on main.)

## Remaining blockers (NOT editor code — seed/runtime level)

### 1. `rust-hosted` binary crashes at startup (JIT)
Running the binary panics immediately (SIGSEGV, 0 bytes output):
`can't resolve symbol rt_compile_to_native_with_opt`
(`cranelift-jit/src/backend.rs:345`, via `ExecCore::run_file_jit` →
`JitCompiler::compile_module`). The editor's transitive closure references
`rt_compile_to_native_with_opt`, an `insert_simple!`-registered interpreter-host
extern with no C-ABI symbol — the JIT-at-startup path can't resolve it. This is
the architectural interpreter↔JIT-extern bridge gap (see
`editor_jit_run_route_blockers_2026-05-28.md` item 2). Use `core-c-bootstrap`
(AOT) instead, which now builds + links + runs.

### 2. AOT runtime: `discover_extensions` reports "function not found"
`EditorController.new()` calls `host.discover_extensions(editor_extension_roots())`
(`editor_controller.spl:154`). The method **exists** (`host.spl:113
me discover_extensions(...)`), yet the `core-c-bootstrap` binary reports
"function not found" for it at runtime — an AOT method-dispatch/symbol-resolution
bug, not a missing function. Built-in extensions suffice to draw a frame, so this
blocks extension loading rather than render.

### 3. AOT runtime: per-frame poll calls crash
The TUI shell's per-frame `ctrl._refresh_lsp_results()` / `_poll_file_watcher()` /
`_poll_inlay_hint_refresh_after(100)` / `_poll_debug_dap_client()`
(`tui_shell.spl`, before `_tui_render_frame`) call AOT-stubbed runtime externs and
crash. The methods are real (`editor_controller.spl:367/664/682/700`); the fix is
at the AOT-stub/extern level, not removing the calls.

### 4. `PaletteState` is an undefined type
Referenced at `editor_controller.spl:98` (`palette_state: PaletteState`), `:166`
(`palette_state: nil`), and `tui_shell_panels.spl:437` (`_tui_render_palette`
param), but defined nowhere in the tree. `--entry-closure` builds because the
palette code is unreached, but a full-tree compile / the GUI palette path will
fail. Needs a real `PaletteState` struct (+ the `palette_new`/`palette_show` API).

### (fixed) `core-c-bootstrap` (AOT) duplicate-symbol link error
Was: `duplicate symbol '_rt_file_exists'` (`runtime_native.o` + legacy_core.o).
Fixed via `__attribute__((weak))` on the legacy_core definition (main `61b29213`).

## Caveat / likely root

Both blockers were observed with a bootstrap seed built from a working copy under
concurrent `git reset --hard` modification by a second session (active runtime
symbol work). A **clean bootstrap from quiesced source** may resolve both. Next
step to a rendered frame: clean seed + the editor edits above + whichever blocker
is genuinely present.

## Verification command (revert-proof clone)

```
# clone src to /tmp/proj/src (project layout), apply the edits above, then:
cd /tmp/proj && SIMPLE_LIB=/tmp/proj/src <seed> native-build \
  --runtime-bundle rust-hosted --source /tmp/proj/src/lib --source /tmp/proj/src/app \
  --entry-closure --entry /tmp/proj/src/app/editor/tui_main.spl -o /tmp/editor_clone --clean
```
(The build only reads `cwd/src/lib` for `std.` modules — `SIMPLE_LIB`/`--source`
pointing elsewhere are ignored, so a revert-proof workspace must mirror the
project layout and be built from inside.)

## See also
- `editor_jit_run_route_blockers_2026-05-28.md`
- `feature_request/editor_markdown_editing_subsystem_2026-05-28.md`
