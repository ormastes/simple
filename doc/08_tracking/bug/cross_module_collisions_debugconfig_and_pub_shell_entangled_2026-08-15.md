# Cross-module private-symbol collisions too entangled to rename: `DebugConfig` and public `shell` (2026-08-15)

Status: SUPERSEDED 2026-11-11 (lane intne1, batch p3-intne1-20261111) — both named entanglements resolved in-tree; absorber: 9e7e7a526edb / PR #7597; residual shell row tracked in cross_module_public_symbol_collisions_2026-08-16.

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

## Triage 2026-11-11 (lane intne1, batch p3-intne1-20261111) — verdict: SUPERSEDED (absorbed by PR #7597 convergence; residual tracked in cross_module_public_symbol_collisions_2026-08-16)

Fresh source + compiler-warning re-verification on release/1.0.0 tip (worktree
simple-p3-intne1-20261111, HEAD 79d5af6723f6):

**Entanglement 1 — `class DebugConfig`: RESOLVED.** Exactly one `class DebugConfig`
remains in owned src: `src/lib/nogc_sync_mut/debug/remote/types.spl:79`. The app-side
copy (`src/app/debug/remote/types.spl`) now declares/references it zero times, and
`src/lib/gc_async_mut/debug/remote/types.spl` no longer exists. A new
`src/lib/nogc_async_mut_noalloc/qemu/debug_boot_runner.spl:23` declares a same-named
class, but it never co-compiles with the lib copy — the 2026-11-11 collision probe
emits no class-collision warning for it.

**Entanglement 2 — public fn `shell`: RESOLVED as filed.** Both lib definitions are
now the same signature, `pub fn shell(command: text) -> ProcessResult`
(`src/lib/nogc_sync_mut/io/process_ops.spl:2913` and
`src/lib/nogc_sync_mut/io_runtime.spl:163`); the lib tuple variant in
`src/lib/nogc_sync_mut/io/file_shell.spl` is gone (only `shell_output` remains), and
the `src/app/io/process_ops.spl` mirror was dropped. `git log -S` pins the
`io_runtime.spl` convergence to `9e7e7a526edb` (merge of PR #7597,
`work/hir-nominal-generic-owner-20261107` — the 2026-11 interpreter-essential wave),
which is also the last commit to touch `src/app/debug/remote/types.spl`.

The single residual differing-signature shell row (app tuple mirror
`src/app/io/file_shell.spl:10` vs the two lib `ProcessResult` defs — 3 defs, 2 sigs)
and the wider collision list are live-tracked under
`cross_module_public_symbol_collisions_2026-08-16`; nothing this row named remains
open here.
