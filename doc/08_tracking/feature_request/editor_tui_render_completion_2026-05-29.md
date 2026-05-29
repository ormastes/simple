# Feature Request: Editor TUI render completion + ctrl module consolidation

- **Date:** 2026-05-29
- **Area:** `app/editor` + `lib/editor` + seed runtime/JIT
- **Status:** open
- **Priority:** medium

## Context

The editor-TUI render goal is partly landed. On `main` as of `knrqtpow`:
the `_layout_find_group_index_local` SIGSEGV is fixed (`.id.value`→`.id`, was
deref'ing an `i64` as a pointer), and the previously-undefined UI-state types
`FileTreeState`/`FileTreeVisibleNode`/`SettingsViewState` are implemented, so the
editor compiles again. The AOT duplicate-`_rt_file_exists` link blocker was fixed
earlier (`61b29213`). A real frame was already drawn via the `EditorBuffer` through
the interpreter (see bug doc below).

What is NOT yet done: an AOT/JIT build of the **full interactive editor** still
does not draw a frame, and two numbered controller-module splits remain.

## Ask

### 1. Consolidate numbered controller-module splits
Per the "no numbered/versioned module splits" rule, merge:
- `editor_ctrl_core2.spl` (739L) → `editor_ctrl_core.spl`
- `editor_ctrl_lsp2.spl` (344L) → `editor_ctrl_lsp.spl`

Both `*2` files are pure free-`fn` modules over `EditorController` with **no name
collisions** against their base (verified) and import-supersets of the base (lsp2
adds `std.editor.services.{md_lsp_config,simple_lsp_config}`). Only
`editor_controller.spl` imports the `*2` modules. Merge = append bodies + union
imports + drop the two `use ...editor_ctrl_{core2,lsp2}.*` lines + delete the
`*2` files. (Attempted once; reverted by a concurrent agent's working-copy
checkout — must be done as a single scoped commit, fast.)

### 2. Make the AOT/JIT editor actually render a frame
Resolve the runtime-level blockers (NOT editor code) tracked in
`doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md`:
- AOT "function not found: `discover_extensions`" — the method exists at
  `host.spl:113`; an AOT method-dispatch/symbol-resolution bug.
- AOT per-frame poll-call crash — `ctrl._refresh_lsp_results()` /
  `_poll_file_watcher()` / `_poll_inlay_hint_refresh_after()` /
  `_poll_debug_dap_client()` hit AOT-stubbed externs.
- `rust-hosted` JIT: unresolved `rt_compile_to_native_with_opt` (interpreter-host
  extern with no C-ABI symbol).

### 3. Define `PaletteState`
Referenced at `editor_controller.spl:98/166` and `tui_shell_panels.spl:437` but
defined nowhere. `--entry-closure` builds because the palette code is unreached,
but a full-tree compile / GUI palette path needs a real `PaletteState` struct
(+ `palette_new`/`palette_show` API).

## See also
- `doc/08_tracking/bug/editor_render_runtime_blockers_2026-05-29.md`
- `doc/08_tracking/bug/editor_jit_run_route_blockers_2026-05-28.md`
- `doc/08_tracking/feature_request/editor_markdown_editing_subsystem_2026-05-28.md`
