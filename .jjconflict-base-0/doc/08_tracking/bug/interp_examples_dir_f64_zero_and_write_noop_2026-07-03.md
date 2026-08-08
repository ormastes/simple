# Bug: scripts under examples/ zero nested f64 payloads and no-op file writes

**Date:** 2026-07-03
**Severity:** high (silently wrong results)
**Status:** resolved 2026-07-03 (write no-op fixed; f64-zero not reproducible — see Resolution)

## Resolution (2026-07-03)

Re-ran the exact repro against the deployed `bin/simple`
(`release/x86_64-unknown-linux-gnu/simple`, 2026-06-28 build):

- **f64-zero: NOT reproducible.** 10/10 runs of
  `bin/simple run examples/10_tooling/office_macros/quarterly_report_macro.spl <dir>`
  print `profit=400` and `budget.csv` contains `Profit,400` — from repo root,
  from inside `examples/10_tooling/office_macros/`, and from a worktree. The
  minimal trifecta probe from `interp_f64_nested_struct_payload_zero_2026-06-14`
  also prints `OK`. That bug's failing executor was the stage4
  `bin/release/simple` binary; `bin/release/simple` is now a wrapper (since
  2026-06-30) that execs the seed-built binary, which is clean. The location
  dependence reported here could not be reproduced in any variant; the report
  was filed at 12:19:09, the exact second of a `jj reconcile divergent
  operations` (see op log), so a torn working copy is the likely source.
- **write no-op: real, but location-independent.** `rt_file_write_text`
  returns `false` when the target's parent directory does not exist, and every
  layer (`io_runtime.write_file` → `office_api.macro_save_*` → example script)
  forwards or drops the bool, so `bin/simple run ... /tmp/out` with no
  pre-existing `/tmp/out` silently writes nothing — identically for the
  in-repo and copied-to-/tmp script. Fixed at the shared point,
  `src/lib/nogc_sync_mut/io_runtime.spl` `file_write`: on write failure with a
  missing parent directory, `rt_dir_create_all` the parent and retry once.
  All `io_runtime` write callers (write_file/file_write, 80+ files) route
  through it. Verified: repro now writes all 4 files into a nonexistent
  (including nested) out dir; `office_api_spec`, `file_formats_spec`,
  `io_runtime_import_spec` pass.
- Follow-up: `std.fs` `File.write` (`src/lib/nogc_sync_mut/fs.spl:247`) uses a
  separate `extern file_write_text` path and still silently returns `false`
  on a missing parent directory.

## Symptom
The identical Simple script produces different results depending on its
location on disk:

- run from `test/` (spec runner) or from a directory OUTSIDE the repo
  (e.g. /tmp): correct — `Sheet.set_value("B2", "1200")` stores 1200,
  `cell_display_text` shows `1200`, `std.io_runtime.write_file` writes.
- run from `examples/10_tooling/office_macros/`: every
  `CellValue.NumberVal(value: f64)` payload reads back as
  `0.00000000000000000` (raw float formatting, wrong code path), and
  `write_file` returns without creating the file.

## Repro
```
bin/simple run examples/10_tooling/office_macros/quarterly_report_macro.spl /tmp/out
# -> profit=0, no files written
cp examples/10_tooling/office_macros/quarterly_report_macro.spl /tmp/m.spl
bin/simple run /tmp/m.spl /tmp/out
# -> profit=400, budget.csv/report.md/budget.html/report.html all written
```

## Analysis
Related to interp_f64_nested_struct_payload_zero_2026-06-14 (f64 payloads in
nested struct/enum zero out) and the cross-module struct-name collision bug:
under the examples/ module-resolution context the office modules appear to
load through a second registration path, zeroing f64 enum payloads
(CellValue.NumberVal) and mis-dispatching number formatting. Outside the repo,
module resolution falls back to runtime loading and behaves correctly, as
does the test/ spec context.

## Impact
In-repo example scripts that exercise f64-carrying models give silently wrong
output. User macros outside the repo are unaffected.
