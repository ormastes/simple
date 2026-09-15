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
