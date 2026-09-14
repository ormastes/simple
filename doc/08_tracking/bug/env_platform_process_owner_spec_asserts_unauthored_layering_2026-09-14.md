# `env_platform_process_owner_spec.spl` asserted a layering that never existed

## Status
FIXED in this change.

## Symptom
`test/01_unit/lib/nogc_sync_mut/env_platform_process_owner_spec.spl` was RED:
`bin/simple test <spec>` failed with `1 example, 1 failure`.

## Root cause (two independent drifts, same file)

1. **Lines 10-12 asserted an unauthored layering.** The spec required
   `env/platform.spl` to import `std.nogc_sync_mut.io.{env_ops, process_ops,
   sysinfo_ops}.{home_raw, cwd_raw, process_run_raw, hostname}`. That content
   arrived via commit `8bc9a7923d7` — **empty commit subject, single parent,
   shown as a brand-new file against that parent** (an unauthored
   recreation/merge artifact, not a design commit). Evidence it was never the
   intended design:
   - `git log --all -S 'io.env_ops.{home_raw' -- src/lib/nogc_sync_mut/env/platform.spl`
     — no hit on any branch; platform.spl never imported that symbol set.
   - `git log --all -S 'fn process_run_raw' -- src/lib/nogc_sync_mut/io/process_ops.spl`
     — a *public* `process_run_raw` was never defined there (only the private
     `_process_run_raw`, which applies `host_path_native` and is deliberately
     module-local).
   - The **original, authored** spec (`dabe39cf44a`, 2026-07-14, title "keeps
     rt_process_run owned by env types only") asserted
     `use std.env.types.{rt_env_home, rt_hostname, rt_env_cwd, rt_process_run}`
     — byte-identical to `platform.spl:5` today.
   - `fcbec1c3b62` "fix(merge): restore src/compiler and src/lib to origin for
     phase 1 bootstrap" **deliberately** removed `home_raw`/`cwd_raw` from
     `io/env_ops.spl` and never touched platform.spl's import — the lib side
     was authored back to its current shape; the `test/` copy of the spec was
     not reverted alongside it.
   - `env/platform.spl`'s own `_platform_*_raw` helpers (dated 2026-08-11,
     2026-09-02 comments) are the deliberate design: foundational,
     widely-imported modules keep local `@always_inline` extern wrappers
     instead of importing owner functions, exactly to avoid the "unresolved
     external, module de-JITs to the interpreter (100-1000x slower)" failure
     mode documented in
     `doc/08_tracking/bug/io_runtime_process_owner_alias_dejits_module_2026-08-22.md`.
     `io/env_ops.spl` itself says "local copies to avoid circular imports."
     Importing `io.process_ops` (973 lines, pulls in `process_governor`,
     `host_path`, `file_ops`, `pipe`, `io_runtime`) into `env/platform.spl`
     would also regress module-load-heavy startup paths (see the companion
     MCP-startup investigation in this same change).

   A prior agent session (`7e3306cbad0`, 2026-09-13) found this and correctly
   diagnosed it — see that commit's message — but treated the unauthored
   layering as a legitimate pending target and left it RED "deliberately,"
   without filing the bug record testing.md requires for a left-RED spec.
   That diagnosis undersold the provenance evidence above: there is no design
   doc or authored commit for an env_ops/process_ops/sysinfo_ops owner
   migration of `env/platform.spl`. This is un-inverting an unauthored
   rewrite, not weakening a correct assertion.

2. **Line 15 (types export list) drifted for a real, unrelated reason.**
   `7e3306cbad0` correctly updated the expected export string to include
   `rt_platform_name` (matching `types.spl` at the time). One day later,
   `2afd824ef42` "fix(runtime): consolidate rt_platform_name onto a single
   extern declaration" legitimately removed `rt_platform_name` from
   `env/types.spl`'s own extern+export (moving every call site onto
   `std.sffi.platform.platform_name_raw`, fixing real Windows host-OS
   detector disagreements #941/#944/#945/#947 — see
   `doc/08_tracking/bug/win_host_os_detector_disagreement_2026-09-14.md`).
   That PR did not touch this spec, so the two PRs' non-conflicting textual
   changes to adjacent files left the spec's export-list assertion stale.

## Fix
- Restored the `it` title and lines 10-12 to the original, authored
  `dabe39cf44a` assertion (`use std.env.types.{rt_env_home, rt_hostname,
  rt_env_cwd, rt_process_run}` + `extern fn rt_process_run` ownership), and
  dropped the dead `init`/`async_init` `file_read`s that were never asserted
  against.
- Dropped `rt_platform_name` from the expected `types.spl` export string
  (line 15 was the only assertion that had gone genuinely RED against the
  current, correct `types.spl` content).

## Verification
```
SIMPLE_BINARY=<repo>/bin/release/x86_64-pc-windows-msvc/simple.exe \
  simple.exe test test/01_unit/lib/nogc_sync_mut/env_platform_process_owner_spec.spl
```
`SPEC FILE VERDICT: ... outcome=OK declared>=1 executed=1 passed=1 failed=0 skipped=0 dropped=0`
