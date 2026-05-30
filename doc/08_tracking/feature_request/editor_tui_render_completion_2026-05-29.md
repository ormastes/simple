# Feature Request: Editor TUI render completion + ctrl module consolidation

- **Date:** 2026-05-29
- **Area:** `app/editor` + `lib/editor` + seed runtime/JIT
- **Status:** resolved 2026-05-29
- **Priority:** medium

## Context

The editor-TUI render goal is partly landed. On `main` as of `knrqtpow`:
the `_layout_find_group_index_local` SIGSEGV is fixed (`.id.value`→`.id`, was
deref'ing an `i64` as a pointer), and the previously-undefined UI-state types
`FileTreeState`/`FileTreeVisibleNode`/`SettingsViewState` are implemented, so the
editor compiles again. The AOT duplicate-`_rt_file_exists` link blocker was fixed
earlier (`61b29213`). A real frame was already drawn via the `EditorBuffer` through
the interpreter (see bug doc below).

The `rust-hosted` and `core-c-bootstrap` builds of the full TUI now draw
active-buffer frames. Palette and LSP popup overlays are restored and verified
with visible native probes.

## Ask

### 1. Consolidate numbered controller-module splits — done 2026-05-29
Per the "no numbered/versioned module splits" rule, merge:
- `editor_ctrl_core2.spl` (739L) → `editor_ctrl_core.spl`
- `editor_ctrl_lsp2.spl` (344L) → `editor_ctrl_lsp.spl`

Both `*2` files are pure free-`fn` modules over `EditorController` with **no name
collisions** against their base (verified) and import-supersets of the base (lsp2
adds `std.editor.services.{md_lsp_config,simple_lsp_config}`). Only
`editor_controller.spl` imports the `*2` modules. Merge = append bodies + union
imports + drop the two `use ...editor_ctrl_{core2,lsp2}.*` lines + delete the
`*2` files. Completed by merging the bodies/imports into the base modules,
removing the `editor_controller.spl` imports, deleting both numbered modules,
and updating palette/controller source-contract specs to the consolidated
module boundaries.

Verification:
- `SIMPLE_LIB=src bin/simple check src/app/editor/editor_controller.spl src/app/editor/editor_ctrl_core.spl src/app/editor/editor_ctrl_lsp.spl src/app/editor/tui_main.spl src/app/editor/tui_shell.spl test/system/editor_palette_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/system/editor_palette_spec.spl --mode=interpreter --clean` (`11/11`)

### 2. Make the AOT/JIT editor actually render a frame — partial 2026-05-29
The `rust-hosted` and `core-c-bootstrap` lanes now build and render repeated
active-buffer terminal frames under a 3-second timeout with no stderr. The
frames include the status bar (`NORMAL`, `[No Name]`, `1 files`, `ready`) and no
longer rely on the fallback `No file open...` placeholder.

Verification:
- `SIMPLE_LIB=src bin/simple native-build --runtime-bundle rust-hosted --source src/lib --source src/app --entry-closure --entry src/app/editor/tui_main.spl --output /tmp/simple_editor_tui_rust_hosted`
- `TERM=xterm timeout 3 /tmp/simple_editor_tui_rust_hosted /tmp/simple_editor_empty.spl`
- `SIMPLE_LIB=src bin/simple native-build --runtime-bundle core-c-bootstrap --source src/lib --source src/app --entry-closure --entry src/app/editor/tui_main.spl --output /tmp/simple_editor_tui_corec`
- `TERM=xterm timeout 3 /tmp/simple_editor_tui_corec /tmp/simple_editor_empty.spl`

Resolved runtime/fidelity blockers are tracked in
`doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md`:
- The prior core-C startup segfault is fixed by skipping absent extension roots
  before calling `rt_dir_walk`.
- The prior active-buffer render crash is fixed with explicit native result
  types in `tui_shell.spl`.
- The prior overlay guard is removed. Visible palette and LSP popup native
  probes render their expected text.
- The prior `rust-hosted` missing `rt_compile_to_native_with_opt` symbol is
  fixed.

### 3. Define `PaletteState` — done 2026-05-29
`src/lib/editor/services/command_palette.spl` now defines `PaletteState`,
fuzzy matching/ranking, and the `palette_new`/`palette_show` API used by the
controller and TUI palette renderer. `test/system/editor_palette_spec.spl`
passes 11/11.

## See also
- `doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md`
- `doc/08_tracking/bug/editor_jit_run_route_blockers_2026-05-28.md`
- `doc/08_tracking/feature_request/editor_markdown_editing_subsystem_2026-05-28.md`
