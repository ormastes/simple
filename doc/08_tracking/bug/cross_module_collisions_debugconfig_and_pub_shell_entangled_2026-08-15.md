# Cross-module private-symbol collisions too entangled to rename: `DebugConfig` and public `shell` (2026-08-15)

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

`compiler_cross_module_private_symbol_collision` warnings fixed in the same pass:
`FixApplicator` (compiler side renamed to `FixToolApplicator`), `Lint`/`LintResult`
(easy_fix side renamed to `EasyFixLint`/`EasyFixLintResult`), and two private
`fn shell` helpers (`semihost_shell` in
`src/lib/nogc_async_mut_noalloc/execution/semihost_capture.spl`, `fileio_shell` in
`src/lib/nogc_async_mut/mcp/fileio_temp.spl`). The two below remain because every
side is heavily imported.

## 1. class `DebugConfig`

- `src/app/debug/remote/types.spl` vs `src/lib/nogc_sync_mut/debug/remote/types.spl`
  (a third copy lives in `src/lib/nogc_async_mut/debug/remote/types.spl`).
- App side: 47 reference sites across 9 files (`src/app/debug/remote/**`,
  `src/app/dap/**`, `src/app/test_daemon/adapters/hardware_adapter.spl`).
- Lib side: referenced from 50+ files (dap adapters, debug/remote protocol +
  exec adapters, terminal/t32, backends) across two lib families.
- Real misdispatch risk: interpreter resolves class members by NAME across
  co-compiled modules. Fix direction: rename the app-side class (e.g.
  `AppDebugConfig` or fold `src/app/debug/remote` onto the std lib module — it
  is a near-mirror of the lib tree).

## 2. public fn `shell` (ProcessResult vs ShellResult vs tuple)

Co-compiled duplicate definitions with differing signatures:

- `src/lib/nogc_sync_mut/io/process_ops.spl:434` `pub fn shell(text) -> ProcessResult` (~90 importers)
- `src/lib/nogc_sync_mut/io_runtime.spl:69` `pub fn shell(text) -> ShellResult` (~139 importers)
- `src/lib/nogc_sync_mut/io/file_shell.spl:10` `fn shell(text) -> (text, text, i64)` — private,
  but re-exported publicly via `src/lib/nogc_sync_mut/io.spl:107` and
  `src/lib/nogc_sync_mut/io/__init__.spl` (`export shell, shell_output`), then
  re-re-exported by `src/lib/nogc_async_mut_noalloc/io/__init__.spl`.
- Mirrors `src/app/io/process_ops.spl:359` and `src/app/io/file_shell.spl:10` duplicate
  the lib definitions again.

Every candidate rename breaks a public API surface with >30 import sites (the
tuple variant is public API through the `std.io` export chain, so it cannot be
renamed without an aliasing re-export or a wrapper that would itself recreate a
colliding `shell`). Fix direction: converge on ONE public `shell` signature
(likely `ProcessResult`), migrate `io_runtime.ShellResult` callers, and drop the
`src/app/io` mirror in favour of the std module.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**STILL-OPEN, deliberately deferred — unchanged.** No change made in this pass; the
47 `DebugConfig` reference sites and 3 competing `shell` signatures with ~230
importers are exactly the entanglement this doc describes, and a partial rename is
more dangerous than the status quo. Recorded as a knowing non-fix, not a silent
skip.
