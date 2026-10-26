# Workaround annotation malformed: refresh fails on every native-build (2026-10-27)

**Date:** 2026-10-27
**Status:** fixed (annotations); lock item not a defect, see Resolution
**Evidence:** `C:/dev/hircfg-probe/logs3/*.log`, `C:/dev/hircfg-probe/logs/`
**Compiler:** `bin/simple native-build` on release/1.0.0
**Severity:** P1 (blocks all native-build on the release branch)
**Owner:** unassigned (authors of c2a397e2b9b, 0d71ab206d4, 52e892180bd, 7b6dc118a4d8)

## Rule

The `@workaround` annotation must have the form `@workaround bug=<canonical-id> ...`. The canonical id references the bug's entry in `bug_db.sdn`. A workaround without the `bug=` prefix is malformed and fails the registry refresh.

## Symptom

Every invocation of `bin/simple native-build` on release/1.0.0 fails with:

```
workarounds: refresh failed: src/lib/scv/compile_source_inventory.spl:420: workaround must immediately precede the affected block
```

and/or

```
workarounds: refresh failed: src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:73: mandatory bug=<canonical-id> must be first
```

### Evidence from logs

From `C:/dev/hircfg-probe/logs3/aarch64-unknown-linux-gnu.A.log`:
```
workarounds: refresh failed: build/scv/snapshots/scv-revision-v1-88a488e88082e9e7077f6ef98e1dd6eb6c23bb5d90e72378e3049a406565f1c7/src/lib/scv/compile_source_inventory.spl:420: workaround must immediately precede the affected block
```

Every native-build log in `C:/dev/hircfg-probe/logs3/` and `C:/dev/hircfg-probe/logs/` prints this failure.

### Root cause

Two distinct failures in workaround annotation handling:

#### Cause 1: Malformed `@workaround doc/...` instead of `@workaround bug=<id>`

Twelve annotations use the wrong form `@workaround doc/<path>` instead of the required `@workaround bug=<id>` format. The registry parser (src/lib/scv/compile_source_inventory.spl and src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl) fails with:

```
mandatory bug=<canonical-id> must be first
```

Sites and introducing commits:

**Commit c2a397e2b9b** ("fix(pure_sql): work around three native MIR failures"):
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:73
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:3032
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:3057
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:3138
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:3387
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl:702
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl:733
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl:778
- src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl:1520

**Commit 0d71ab206d4** ("fix(build): parenthesize try before member in elf archive_file (@workaround indcall)"):
- src/compiler/70.backend/linker/elf/archive_file.spl:75

**Commit 52e892180bd** ("fix(io): @workaround element-wise identity compare in retained_file"):
- src/lib/nogc_sync_mut/io/retained_file.spl:151
- src/lib/nogc_sync_mut/io/retained_file.spl:288

#### Cause 2: Annotation separated from function by comment lines

In src/lib/scv/compile_source_inventory.spl:420, the annotation is well-formed (`@workaround bug=native_raw_integer_optional_presence_2026_10_26`) but fails because four OPEN: comment lines sit between it and the function declaration it annotates. The registry (src/app/bug/workaround_index.spl:119-122) requires the annotation to immediately precede the affected block with no intervening comments.

Introduced in commit 7b6dc118a4d8 (2026-10-26).

## Side effect: stale lock file

A stale `.simple/workarounds.sdn.lock` left by an interrupted build causes subsequent builds to fail with:

```
workaround writer lock unavailable
```

until the lock file is manually deleted.

## Impact

Native-build is completely blocked on release/1.0.0, preventing:
- Bootstrap / staged-self-compilation workflows
- Continuous integration on the release lane
- Any toolchain deployment to the release binary

## Expected fix

**For Cause 1** (malformed @workaround doc/... annotations):
1. Rewrite each of the 12 sites using `@workaround doc/...` as `@workaround bug=<id> ...` per the registry contract, mapping each to the documented bug ID in the referenced doc.
2. Verify the mapped bug ID exists in `bug_db.sdn`.

**For Cause 2** (annotation separated from function):
1. Move the `@workaround bug=native_raw_integer_optional_presence_2026_10_26` annotation in src/lib/scv/compile_source_inventory.spl directly above the `fn compile_source_inventory_decimal_v1` declaration, removing the intervening OPEN comment lines to a preceding location or documentation section.

**General hardening**:
1. Make the lock file stale-safe: read the lock, check its timestamp, and retry after a timeout rather than blocking indefinitely.

## Resolution (2026-10-27)

- All 12 `@workaround doc/...` sites now read `@workaround bug=<id> reason=see doc/...` and sit
  directly above their block (explanatory comments moved above the tag). Pinned by
  `test/01_unit/app/bug/workaround_annotation_format_spec.spl`. That spec parses the five files
  with the registry parser: it fails on the pre-fix tree and passes after.
- Stale lock: no code change. `workarounds.sdn.lock` is an OS lock (`rt_file_lock` uses
  `LockFileEx` / `flock`), and the OS releases it when the holder exits. A leftover lock file
  therefore cannot block. "writer lock unavailable" means a live holder outlasted the 5 s wait,
  e.g. concurrent builds in one checkout. Deleting the file by age would break mutual exclusion,
  because on POSIX unlinking a held lock lets a second process lock a fresh inode.
