# BUG: `RamFsDriver.name` — two hand-written spec suites assert contradictory values for the same field

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** medium — 3 assertions are red today, and the obvious fix turns
4 currently-green assertions in another suite red. No design doc settles it.

## Symptom

`test/01_unit/fs_driver/instance_test.spl` fails 3 of 4 examples:

```bash
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/fs_driver/instance_test.spl
#   Results: 5 total, 2 passed, 3 failed
#   ✗ RamFs variant can be constructed     expected RamFsDriver to equal ramfs
#   ✗ driver_name() returns 'ramfs'        expected RamFsDriver to equal ramfs
#   ✗ RamFs name field is 'ramfs'          expected RamFsDriver to equal ramfs
```

Actual: `DriverInstance.RamFs(...).driver_name()` returns `"RamFsDriver"`.
Expected (per this spec): `"ramfs"`.

## Root cause

`src/lib/nogc_async_mut/fs_driver/ramfs.spl:104` constructs the driver with

```
name:     "RamFsDriver",
```

and `DriverInstance.driver_name()` returns that field verbatim
(`src/lib/nogc_async_mut/fs_driver/instance.spl:58-65`, `case RamFs(d): d.name`).

This is a regression introduced by the `RamFsStub` → `RamFsDriver` swap.
`instance.spl:8-9` records the swap ("Phase 9 ramfs: RamFsDriver (from
ramfs.spl) replaces RamFsStub"), and `instance.spl:29` still documents the
pre-swap contract in prose:

> Existing tests that construct `RamFsStub(name: "ramfs")` for mount-table
> shape tests continue to compile.

The stub carried `"ramfs"`; the replacement driver carries `"RamFsDriver"`.
Nothing updated the value, and nothing updated the prose either.

## Why not fixed now

Flipping `ramfs.spl:104` to `"ramfs"` fixes the 3 assertions above but breaks
4 hand-written assertions in a suite outside this scope, which pin the current
value:

- `test/02_integration/storage/dbfs/mount_table_dbfs_dispatch_spec.spl:35,50,65`
  — `expect(resolved.driver_name()).to_equal("RamFsDriver")`
- `test/02_integration/storage/dbfs/dbfs_hw_passthrough_spec.spl:30`
  — `expect(dev).to_equal("RamFsDriver")`

(plus generated `.spipe_matchers_*` copies and the legacy `test/integration/`
duplicates, which mirror the same four.)

So this is not a one-line fix — it is a contract decision, and the two
candidate answers have real evidence on each side:

**For `"ramfs"`** — the field is a *filesystem type name* (`mount -t ramfs`),
which is lowercase by convention; the bench harness already uses `"ramfs"` as
the driver identifier (`test/fixtures/storage/dbfs/bench_harness.spl:77-88`,
`bench_ac7_runner.spl`); `instance.spl:29` documents `"ramfs"`; and the unit
spec states the contract explicitly in its docstring
(`instance_test.spl:41`: *"driver_name() must return \"ramfs\" for this
variant"*).

**For `"RamFsDriver"`** — the sibling driver uses the same class-name style
(`src/lib/nogc_async_mut/fs_driver/fat32_stub.spl:382,391`:
`name: "Fat32Driver"`), and 4 integration assertions currently depend on it.

Neither design doc resolves it: `doc/05_design/os/storage/fs_driver_interface.md`
and `doc/07_guide/os/fs_driver.md` both show `driver_name()` returning `d.name`
(guide §"Also extend `driver_name()`") but never pin the string's value or
casing.

Picking a side means editing spec files in an area I was scoped out of, and
whichever side loses, its assertions have to change — which is a product-owner
call, not a test-fixing one. Filing instead of guessing.

**Suggested resolution:** adopt `"ramfs"` (and `"fat32"` for `Fat32Driver`),
i.e. make `name` the mount-type identifier consistently, then update the 4
dbfs assertions plus their generated/legacy mirrors in the same change. That
makes the field mean one thing across all drivers instead of two.
