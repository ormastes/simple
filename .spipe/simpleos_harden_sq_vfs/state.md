# Lane SQ — SQLite-over-SimpleOS VFS contract (master plan §15.2)

Status: DONE (this increment — contract only; no SQLite build). Not committed.

## Scope

First DB milestone groundwork. Defines the SimpleOS-side `sqlite3_vfs` /
`sqlite3_io_methods` shim CONTRACT as a pure-Simple model + spec, with an
honest per-method status driven by the real POSIX matrix (posix_profiles P5,
Lane T2-C flock). No SQLite amalgamation, no C build, no QEMU.

## Files

- `src/os/port/sqlite/sqlite_vfs_contract.spl` (new) — model: lock ladder,
  facility statuses, 17 method reports, durability flags, WAL/rollback gating.
- `doc/02_requirements/feature/sqlite_vfs_contract.md` (new) — method table,
  lock ladder, durability contract, supported vs blocked modes.
- `test/01_unit/os/port/sqlite_vfs_contract_spec.spl` (new) — 24 examples.
- `.spipe/simpleos_harden_sq_vfs/state.md` (this file).

## Method status table (17 methods)

supported (6): xOpen, xClose, xRead, xWrite, xFileSize, xSectorSize
partial   (6): xSync, xLock, xUnlock, xCheckReservedLock, xFileControl,
               xDeviceCharacteristics
unsupported (5): xTruncate, xShmMap, xShmLock, xShmBarrier, xShmUnmap

Lock ladder → flock: NONE→LOCK_UN, SHARED→LOCK_SH, RESERVED→LOCK_SH (inexact),
PENDING→LOCK_EX (inexact), EXCLUSIVE→LOCK_EX. Whole-file flock cannot represent
RESERVED/PENDING byte ranges — collapsed onto SH/EX, tracked in-process
(honest, per Lane T2-C).

Durability flags published now: sector_size=512, has_flush=true; atomic-write,
safe-append, sequential, powersafe-overwrite all FALSE (unproven → reported
false; SQLite behaves conservatively).

## Modes

- Rollback journal (DELETE, default): SUPPORTED — critical path has no
  unsupported method (xSync/xLock partial → functional, §8 durability-proof
  caveat). Does not need xTruncate or shm.
- WAL: BLOCKED. Prereq = shared mmap (MAP_SHARED / shm_open) for the -wal-index,
  a POSIX Profile C facility currently absent by design (fails closed
  EOPNOTSUPP, posix_profiles P5). xShmMap fails closed → WAL gated off honestly.

## Spec verdict

`/tmp/sqlane/bin/sqjob run test/01_unit/os/port/sqlite_vfs_contract_spec.spl`
→ 8 + 5 + 5 + 3 + 3 = **24 examples, 0 failures**.

Fail-once proof: setting xShmMap status to "supported" → WAL-gating test
("gates WAL mode off because xShmMap is unsupported") fails, plus shm-report and
tally tests (5 failures across 2 blocks). Restored → all green again. The gate
is wired to the real facility status, not a hardcoded literal.

## Next increment (resume plan)

Actual SQLite amalgamation build against this shim. MULTI-SESSION, needs the C
toolchain:
1. Vendor SQLite amalgamation (sqlite3.c/h) under src/os/port/sqlite/vendor/.
2. Implement the C shim `sqlite3_vfs` whose xOpen/xRead/.../xSync call the
   SimpleOS VFS + flock + block-flush paths this model targets; register it
   via sqlite3_vfs_register as the default VFS.
3. Wire xShmMap/xShmLock/xShmBarrier/xShmUnmap to return SQLITE_IOERR / OMIT so
   SQLite refuses WAL (WAL truly gated in C, matching the model).
4. Run upstream + rollback-journal test list from §15: multi-process
   contention, forced process death, flush reordering, ENOSPC, truncated
   journal, checkpoint/restart. WAL/-wal-index/corrupted-shm tests stay BLOCKED
   until shared mmap lands (separate POSIX-C lane).
5. Prereq lanes to unblock WAL later: shared mmap (MAP_SHARED/shm_open),
   VFS truncate op (for TRUNCATE journal mode), and §8 durability proofs
   (ordering/FUA/torn-write/power-loss) to lift xSync partial→supported.

## Blockers

- WAL blocked on shared mmap (external POSIX-C facility lane).
- xTruncate blocked on FsDriver trait lacking a truncate op.
- xSync durability proof pending §8 gates (block layer ordering/power-loss).
- Deployed bin/simple is a stale seed / `simple test` hangs — used the lane
  binary recipe (/tmp/sqlane/bin/sqjob) per task instructions.
