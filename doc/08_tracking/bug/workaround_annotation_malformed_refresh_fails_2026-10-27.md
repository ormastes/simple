# Workaround annotation malformed: refresh fails on every native-build (2026-10-27)

**Date:** 2026-10-27
**Status:** open
**Evidence:** `C:/dev/hircfg-probe/logs3/*.log`, `C:/dev/hircfg-probe/logs/`
**Compiler:** `bin/simple native-build` on release/1.0.0
**Severity:** P1 (blocks all native-build on the release branch)
**Owner:** unassigned (pure_sql lane author of c2a397e2b9b)

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

Annotations using `@workaround doc/<path>` instead of `@workaround bug=<id>`:

```
src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:73:# @workaround doc/08_tracking/bug/puresql_native_mir_failures_2026-10-25.md (cause 2):
src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:3032:            # @workaround doc/08_tracking/bug/puresql_native_mir_failures_2026-10-25.md (cause 1):
src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:3057:                # @workaround doc/08_tracking/bug/puresql_native_mir_failures_2026-10-25.md (cause 1):
src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl:3138:            # @workaround doc/08_tracking/bug/puresql_native_mir_failures_2026-10-25.md (cause 1):
src/compiler/70.backend/linker/elf/archive_file.spl:75:            # @workaround doc/08_tracking/bug/indcall_try_then_member_2026-10-25.md:
```

Introduced in commit c2a397e2b9b ("fix(pure_sql): work around three native MIR failures...").

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

1. Rewrite each malformed `@workaround doc/...` annotation as `@workaround bug=<id> ...` per the registry contract.
2. Verify the mapped bug ID exists in `bug_db.sdn`.
3. Make the lock file stale-safe: read the lock, check its timestamp, and retry after a timeout rather than blocking indefinitely.
