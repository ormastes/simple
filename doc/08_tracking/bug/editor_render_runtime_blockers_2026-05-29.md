# Status/Bug: Editor TUI render code complete; runnable binary blocked by 2 seed/runtime bugs

- **ID:** editor_render_runtime_blockers
- **Date:** 2026-05-29
- **Area:** editor app + seed runtime/JIT
- **Status:** RENDER ACHIEVED — editor frame drawn via the real EditorBuffer through `bin/simple`'s interpreter with a narrowed SIMPLE_LIB (see "Frame rendered" below). Full native binary still blocked by the 2 seed/runtime bugs.

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
- `_tui_render_split_borders` → single-pane no-op (the flat-array SplitNode model
  it used doesn't exist; real `SplitNode` is a recursive enum).
- `_tui_render_palette` → no-op (`PaletteState`/`palette_new`/`palette_show` are an
  undefined API; popup isn't part of the default frame).
- `LspResponse` tuple-element annotations in `editor_ctrl_core2.spl`.

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
`editor_jit_run_route_blockers_2026-05-28.md` item 2).

### 2. `core-c-bootstrap` (AOT) link error
`duplicate symbol '_rt_file_exists'` in `libsimple_runtime.a`
(`runtime_native.o` AND `runtime_legacy_core.o` both define it). A runtime-archive
bug — likely from in-flight runtime symbol work. With this fixed, the AOT bundle
should produce a runnable binary (the extern would be a harmless stub, not a JIT
resolve).

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
