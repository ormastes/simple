# bug-add can replace an existing database that it cannot load (2026-10-27)

**Status:** OPEN — the exclusive create-only writer passed six isolated
temporary-project CLI cases on the refreshed Phase 1 seed. Canonical
registration remains blocked because the historical database contains
malformed rows that the loader used to omit; see
`sdn_database_load_silently_drops_malformed_rows_2026-10-27.md`.
**Severity:** P1 — a failed read of the tracking database is treated as an
empty database, so a later successful save can erase the existing records.
**Component:** `src/app/bug_add/main.spl` load/create decision; underlying
`std.database.core.SdnDatabase.load` validation.

## Source evidence

At `c0b3ad911f4`, `bug-add` called `load_bug_database(BUG_DB_PATH)` and created
a fresh database whenever that call returned `nil` (`src/app/bug_add/main.spl`;
initial lines 140-143). The domain loader directly propagates
`SdnDatabase.load(path)?`
(`src/lib/nogc_sync_mut/database/bug.spl:84-86`). That lower-level load returns
`nil` for a missing path, an empty file, a malformed CRC header, or a CRC
mismatch (`src/lib/nogc_sync_mut/database/core.spl:479-505`). Consequently,
the original caller could not distinguish an absent database, which may be
created, from an existing but unreadable database, which must be preserved and
rejected.

The current candidate no longer queries the path before writing. If a load
returns `nil`, it serializes the new database with the canonical SDN and CRC
writer, writes it under a private same-parent staging directory, syncs the
staged file, and publishes it with the existing no-replace primitive
(`src/lib/nogc_sync_mut/database/atomic.spl`;
`src/lib/nogc_sync_mut/database/core.spl`). Existing entries, including dangling
symlinks, make publication fail. Successfully loaded databases continue using
the existing atomic replacement path.

## Required behavior

- An absent database may be initialized and receive the requested bug.
- A valid existing database may receive a new bug while retaining unrelated
  existing records.
- A duplicate bug ID is rejected, leaving the serialized database unchanged.
- An existing unreadable database is rejected without changing any bytes.
- Initial publication refuses every existing path entry, including dangling
  symlinks, and fails closed when staging or publication cannot complete.

The staging directory is created under the destination's parent so final
publication stays on the same filesystem. If the parent is absent, staging
fails and neither the parent nor database is created. Cleanup targets only the
private staging directory created by this attempt. This makes no claim about
hostile concurrent replacement of the parent path.

## Temporary-project reproduction

Run `src/app/bug_add/main.spl` with its working directory set to a disposable
project root containing `doc/08_tracking/bug/bug_db.sdn` with a malformed CRC
header or CRC mismatch. Use a unique bug ID and explicit date. Capture the
database bytes before and after. Expected behavior is a nonzero command result
and byte-for-byte identical database contents. The pre-fix source took the
fresh-database fallback when loading returned `nil`; the current exclusive
writer passed the malformed-CRC temporary-project case on the refreshed seed.

The first bounded attempt on 2026-10-27 ran before the guard was implemented and
was inconclusive: two examples failed on missing SFFI ABI
`rt_io_file_open_read`, and dangling-link fixture setup returned `ln` exit 1.

A later fresh-seed host CLI probe ran six cases against the first path-query
guard. All invocations exited 1 before database behavior, with stderr reporting
`dynamic SFFI dispatch has no compiler-owned ABI contract for function
'malloc'`. The app's import of
`std.nogc_sync_mut.io.path_identity.path_entry_present` reached the POSIX
`path_identity_abi.spl` raw libc `malloc(size_t) -> pointer` declaration. The
bootstrap interpreter correctly rejected it because generic dynamic SFFI
requires an exact compiler-owned ABI contract. Stderr also reported JIT
demotion while lowering `BugDatabase.critical_bugs`; neither diagnostic
established any database case. Captures and the watchdog receipt are retained
under `/tmp/bug-add-host-cli-qualification-phase1refresh-20261027/`.

The current exclusive writer removes the app's dependency on `path_identity`.
The focused regression covers absent-file creation, two successful adds that
retain the first row, duplicate rejection with unchanged bytes, malformed CRC
rejection with unchanged bytes, dangling-link preservation, and missing-parent
failure. All six cases passed in temporary project roots on the refreshed
pinned seed. This does not qualify preservation of the historical canonical
database. A later canonical registration attempt exposed 20 malformed rows
that the loader silently omitted. The database was restored byte-for-byte from
the verified pre-write snapshot (SHA-256
`278204ab0551e0e4cd016fc87f90c0321269d6858cd1ba59474fa551adee5093`); no
further canonical writes were made. Registration stays deferred until the
separate parser issue is fixed and the historical rows receive an
owner-verified disposition.
