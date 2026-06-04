# Status/Bug: Editor TUI render code complete; full runtime behavior still degraded

- **ID:** editor_render_runtime_blockers
- **Date:** 2026-05-29
- **Area:** editor app + seed runtime/JIT
- **Status:** RESOLVED. The narrowed interpreter proof draws a real buffer-backed frame. The full `rust-hosted` and `core-c-bootstrap` TUI binaries now build and render active-buffer terminal frames under timeout with no stderr. Palette and LSP popup overlays are restored and have native visible-overlay probes.

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

This proves the editor render path works end-to-end in the interpreter. The
full interactive binary now also reaches active-buffer frame rendering in the
`rust-hosted` and `core-c-bootstrap` lanes.

## Full rust-hosted frame rendered (2026-05-29)

The editor now builds with the hosted Rust runtime and reaches the live TUI
render loop:

```
SIMPLE_LIB=src bin/simple native-build --runtime-bundle rust-hosted \
  --source src/lib --source src/app --entry-closure \
  --entry src/app/editor/tui_main.spl \
  --output /tmp/simple_editor_tui_rust_hosted
TERM=xterm timeout 3 /tmp/simple_editor_tui_rust_hosted /tmp/simple_editor_empty.spl
```

Result after the active-buffer fix:
- build completed with `2 compiled, 62 cached, 0 failed`
- process timed out after 3 seconds as expected for an interactive loop
- stderr was empty
- stdout contained repeated alternate-screen frames and a status bar with
  `NORMAL`, `[No Name]`, `1 files`, and `ready`
- stdout did not contain the fallback `No file open...` placeholder

This fixed the prior `rust-hosted` startup blocker by exporting
`rt_compile_to_native_with_opt` through the Rust seed runtime/JIT symbol tables.
It also required hosted terminal SFFI exports and a layout clamp for corrupted
native controller defaults.

## Full core-C frame rendered (2026-05-29)

The `core-c-bootstrap` lane also reaches the live TUI render loop:

```
SIMPLE_LIB=src bin/simple native-build --runtime-bundle core-c-bootstrap \
  --source src/lib --source src/app --entry-closure \
  --entry src/app/editor/tui_main.spl \
  --output /tmp/simple_editor_tui_corec
TERM=xterm timeout 3 /tmp/simple_editor_tui_corec /tmp/simple_editor_empty.spl
```

Result:
- build completed with `1 compiled, 63 cached, 0 failed`
- process timed out after 3 seconds as expected for an interactive loop
- stderr was empty
- stdout contained repeated frames with `NORMAL`, `[No Name]`, `1 files`, and
  `ready`
- stdout did not contain the fallback `No file open...` placeholder

The prior startup segfault was caused by extension discovery calling
`rt_dir_walk` for absent extension roots. In this core-C bundle `rt_dir_walk`
is currently stubbed; the generated stub returns an invalid array-like value and
segfaults. `ExtensionHost.discover_extensions` now skips roots that do not exist
before walking them.


## Milestone (done)

The editor's full render path now **compiles and links** with `--runtime-bundle
rust-hosted`: `Build complete: 60 compiled, 0 cached, 0 failed` → 798 KB binary.
Reaching this required implementing the speculative UI-state types the editor
was written against but that never existed:

- `FileTreeState` + `FileTreeVisibleNode` (+ `new`/`visible_nodes`/`select_next`/
  `select_prev`/`toggle_expand`/`selected_is_dir`/`selected_path`) in
  `src/lib/editor/view/file_tree.spl`.
- `SettingsViewState` (categories/category_index/filtered/selected_index/
  editing/edit_value) in `src/lib/editor/view/settings_view.spl`.
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

## Remaining blockers / follow-up bugs

None for this editor render tracker.

### (fixed) Palette and LSP popup overlays were guarded off
Fixed 2026-05-29 by restoring the overlay calls in `tui_shell.spl` with typed
locals for optional palette state and by using explicit/bridged text lengths in
popup text helpers. The underlying native issue was the same inference family
seen in the buffer renderer: text method calls on function parameters could
produce bad values (`value.len()` returned `-1` in a focused native repro), so
the popup cleaner/fit helpers now use `rt_string_len(value)`.

Verification:
- visible palette + LSP popup native probe rendered `Command Palette`,
  `hover text`, `detail text`, and reached `after-lsp`
- full `rust-hosted` editor TUI timed out normally with no stderr and `1 files`
- full `core-c-bootstrap` editor TUI timed out normally with no stderr and
  `1 files`

### (fixed) Active-buffer render crashed in native hosted lanes
Fixed 2026-05-29 by restoring `_tui_render_single_pane(render_buffer, ...)` and
adding explicit local result types for buffer method calls in the single-pane
renderer. The root symptom was native inference treating
`val n = buffer.line_count()` as `nil`; `val n: i64 = buffer.line_count()`
returns the correct line count. The status bar document count needed the same
explicit `i64` annotation.

### (fixed) AOT/core-C startup segfault after alternate-screen entry
Fixed 2026-05-29 by guarding `ExtensionHost.discover_extensions` against absent
roots before calling `rt_dir_walk`. A stage probe now reaches `stage:done`, and
the full core-C editor render loop times out normally with frame markers and no
stderr.

### (fixed) `rust-hosted` missing `rt_compile_to_native_with_opt`
Fixed 2026-05-29 by exporting `rt_compile_to_native_with_opt` from the Rust seed
runtime/native-all surfaces and adding it to the compiler runtime SFFI symbol
specs. A focused extern probe builds/runs and the full editor no longer fails on
the missing JIT symbol.

### (stale) AOT `discover_extensions` method-dispatch failure
Fresh verification:

```
use std.editor.extensions.host.*

fn main():
    val host = extension_host_with_builtins()
    val count = host.discover_extensions([])
    print count.to_text()
```

`SIMPLE_LIB=src bin/simple check` passes, `core-c-bootstrap` native-build passes,
and the binary exits `0` with output `0`.

### (fixed) `PaletteState` was an undefined type
Fixed 2026-05-29 in `src/lib/editor/services/command_palette.spl` by adding
`PaletteState`, fuzzy matching/ranking, and the `palette_new` /
`palette_show` / `palette_hide` / `palette_update_query` / selection helpers
used by the controller and TUI palette renderer.

Verification:

```bash
SIMPLE_LIB=src bin/simple check src/app/editor/tui_main.spl src/app/editor/editor_controller.spl src/app/editor/editor_ctrl_core.spl src/app/editor/editor_ctrl_core2.spl src/app/editor/tui_shell.spl src/app/editor/tui_shell_panels.spl src/lib/editor/services/command_palette.spl src/lib/editor/extensions/builtin/md_commands.spl test/03_system/editor_palette_spec.spl
SIMPLE_LIB=src bin/simple test test/03_system/editor_palette_spec.spl --mode=interpreter --clean
```

`test/03_system/editor_palette_spec.spl` passes 11/11.

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
