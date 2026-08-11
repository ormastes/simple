# Seed JIT: cli_get_args name+signature collision misdispatches to io/mod_stub (UI args dropped) — FIXED in ui entries

- **Date:** 2026-08-11
- **Severity:** high for the tauri/desktop lane under the seed (launch prints usage, exits 1); latent for any co-compiled graph that imports both `app.io.cli_ops`/`std.sffi.cli` and an `io/mod_stub`
- **Area:** seed JIT public-symbol dispatch; src/app/ui/main.spl, src/app/ui.tauri/app.spl
- **Status:** call sites fixed 2026-08-11 (direct-extern pattern); seed-side dispatch hazard remains open

## Symptom
`tools/tauri-shell/run-desktop.command` spawned
`simple run src/app/ui/main.spl tauri <entry.ui.sdn>`; the process loaded all
modules, printed `[STUB] cli_get_args not available without Rust SFFI`, dumped
usage and exited 1. The Tauri shell logged each usage line as an IPC parse error.

## Root cause
`cli_get_args() -> [text]` is publicly defined with an identical signature in at
least `app.io.cli_ops`, `nogc_sync_mut.sffi.cli`, and every `io/mod_stub`
(app/io, nogc_sync_mut, nogc_async_mut, gc_async_mut). The seed JIT keys public
functions by bare name+signature in co-compiled graphs and falls back to the
last definition on ambiguity (warning class
`compiler_cross_module_private_symbol_collision`, see
compiler_cross_module_private_symbol_collision_2026-06-16.md). The engine2d /
browser-engine modules import `env_get` from `std.gc_async_mut.io.mod_stub`,
which drags the stub `cli_get_args` into the UI graph; the ambiguous call then
resolved to the stub, which prints and returns `[]`. With zero args, main.spl
hit its `cli_args.len() == 0` usage branch.

The electron lane never hit this because `ui.electron/app.spl` declares
`extern fn rt_cli_get_args()` locally and calls it directly.

## Fix applied
- `src/app/ui/main.spl`: dropped the `app.io.cli_ops.{cli_get_args}` import;
  added local `rt_cli_get_args`/`sys_get_args` externs + `_ui_raw_cli_args()`
  with the same fallback semantics.
- `src/app/ui.tauri/app.spl`: same treatment (`_tauri_cli_args()`), both
  `run_tauri`/`run_tauri_mobile` call sites switched.

Verified: tauri desktop showcase renders under the seed
(`[tauri-shell] render, html_len=34551`, `eval OK`, zero STUB lines on the IPC
channel afterwards).

## Remaining hazard
The same stub still shadows other colliding public names (`shell`,
`shell_output`, `file_read_bytes`, `file_read_lines`, `path_join`,
`dir_remove_all`, `compress_block`, `resolve_style`, `text_to_bytes`, …) in
seed-JIT graphs, and `std.sffi.cli.cli_get_args` is still imported by
`ui.tauri/async_app.spl` / `tauri_entry.spl` (shared-WM/mobile paths, not
exercised by the desktop showcase). The systemic fix belongs in the JIT's
module-qualified dispatch, not in per-file renames.
