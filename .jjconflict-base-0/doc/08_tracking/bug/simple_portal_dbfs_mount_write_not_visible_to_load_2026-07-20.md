# `simple_portal` DBFS mount: file written via `_write_mount_file` not visible to `portal_content_db_load_from_mount`

**Date:** 2026-07-20
**Component:** `MountTable`/`DbFsDriver` (`src/lib/nogc_sync_mut/fs_driver/mount_table.spl`)
and/or the `_write_mount_file` test helper's interaction with it
**Severity:** Medium — single example, but panics (crashes the process)
rather than failing a plain assertion
**Found by:** whole-suite triage campaign,
`test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl`

## Symptom

```simple
fn _make_portal_dbfs_mount() -> MountTable:
    var mt = MountTable.new()
    val dbfs = DbFsDriver.new_hosted()
    mt.mount("/portal", DriverInstance.DbFs(dbfs), MountOptions.default()).unwrap()
    mt = _write_mount_file(mt, "/portal/content/pages.db", "ops|Ops|Mounted DBFS content|pages/ops.html\n")
    ...
    mt

it "loads portal content from a DBFS-backed mount table root":
    val mt = _make_portal_dbfs_mount()
    val result = portal_content_db_load_from_mount(mt, "/portal")
    expect(result.is_ok()).to_equal(true)     # this line does not raise...
    val source = result.unwrap()               # ...but this one panics:
```

Actual: `semantic: called unwrap on Err: Missing portal content file:
/portal/content/pages.db` — i.e. `result` is actually an `Err`, but
`expect(result.is_ok()).to_equal(true)` did not report a failure for that
(either it silently passed against an `Err`, or per-block failure-message
overwrite semantics observed elsewhere in this campaign hid it); the
`.unwrap()` on the next line then panics on the real `Err`, which is what
surfaces as the reported crash.

The `pages.db` content genuinely was written via `_write_mount_file` before
the load call, so either that write isn't landing where
`portal_content_db_load_from_mount` reads from, or the `mt.mount(...)`
call on line 23 (called as a bare statement, not reassigned back to `mt`,
unlike the `_write_mount_file` calls which are all `mt = _write_mount_file(mt, ...)`)
doesn't persist the "/portal" mount registration into the `mt` binding that
later calls operate on — two candidate mechanisms, not distinguished
further in this pass.

## Root-cause hypothesis

Two candidates, not resolved from source alone: (1) `MountTable.mount()` is
declared `me fn mount(...)` (line 306 of
`src/lib/nogc_sync_mut/fs_driver/mount_table.spl`), where `me fn` should
mean in-place mutation of `self` — if that's honored correctly, the missing
reassignment on `mt.mount(...).unwrap()` (line 23) shouldn't matter, which
would point instead at (2) a write/read-path bug between
`_write_mount_file` and `portal_content_db_load_from_mount` (e.g. buffering,
or the two going through different `DbFsDriver` instances/copies). Not
confirmed either way; flagging both for whoever investigates.

## Note

Spec left unmodified — the fixture setup mirrors the pattern used
elsewhere in the same file for `_write_mount_file` reassignment, so it
isn't an obvious test-authoring mistake; treating as a genuine defect in
the mount/DBFS write-then-read path (or, less likely, a value-semantics gap
in `me fn` mutation) rather than a stale test.
