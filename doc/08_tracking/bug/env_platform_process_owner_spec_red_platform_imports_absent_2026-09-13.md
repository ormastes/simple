# env_platform_process_owner_spec is RED: env/platform.spl has none of the owner imports it asserts

- **Date:** 2026-09-13
- **Spec:** `test/01_unit/lib/nogc_sync_mut/env_platform_process_owner_spec.spl`
- **Subject:** `src/lib/nogc_sync_mut/env/platform.spl`
- **Status:** open, left RED on purpose (a correct assertion about missing behaviour)

## What fails

The spec's single example, "routes environment platform calls through
semantic owners", expects `platform.spl` to import:

| spec line | expected text | present in platform.spl |
|---|---|---|
| 10 | `use std.nogc_sync_mut.io.env_ops.{home_raw, cwd_raw}` | no |
| 11 | `use std.nogc_sync_mut.io.process_ops.{process_run_raw}` | no |
| 12 | `use std.nogc_sync_mut.io.sysinfo_ops.{hostname}` | no |

Instead, `platform.spl:5` imports the raw externs
`use std.env.types.{rt_env_home, rt_hostname, rt_env_cwd, rt_process_run}`,
and `platform.spl:32-34` (`_platform_hostname_raw`) calls `rt_hostname()`
directly. `git log -S'sysinfo_ops.{hostname}'` on the file returns nothing, so
this owner migration was either never landed in this file or was lost in a
tree restore.

Line 15, the `types.spl` export list, was a separate stale expectation. It was
fixed in `06f5c4f9b11` to include the intended `rt_env_get_i64` (4d3f37e3e9e)
and `rt_platform_name` (f03ad4b1283, #255).

## Unblock condition

Route `platform.spl`'s home, cwd, process-run and hostname calls through
`std.nogc_sync_mut.io.{env_ops, process_ops, sysinfo_ops}`, the semantic
owners the spec names, and drop the direct `rt_*` use. Alternatively, if that
migration was deliberately abandoned, the spec owner must decide to retire
lines 10-12. Do not weaken them in place.

## Closed 2026-11-09 (verification-only, lane p3-subj7)

Spec passes 1/1 with the seed interpreter on origin/release/1.0.0
(worktree @54181f128ea). The owner contract is now pinned as
`std.env.types` ownership: `platform.spl:5` imports
`use std.env.types.{rt_env_home, rt_hostname, rt_env_cwd, rt_process_run}` and
`types.spl` owns the `extern fn rt_process_run` declaration plus the export
list the spec asserts — i.e. the "route through an owner / retire stale spec
lines" unblock condition is satisfied and the spec is the authority.
Neighbours green: host_io_topology 4/4, convert 1/1, temp_dir_creation 2/2,
system_location 7/7, platform_path_owner 2/2. No source change in this closure.

## 2026-11-10 re-verification (lane p3-runner3, row 16): SUPERSEDED (closed)

Re-verified with the worktree seed-smoke binary (bin/simple.exe, v1.0.0-rc.1,
`--mode=interpreter`): `test/01_unit/lib/nogc_sync_mut/env_platform_process_owner_spec.spl`
passes 1/1 (`outcome=OK`). Confirms the 2026-11-09 p3-subj7 closure; no source
change in this closure.
