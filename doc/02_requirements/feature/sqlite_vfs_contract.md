# SQLite-over-SimpleOS VFS Shim Contract

**Feature IDs:** SimpleOS harden lane SQ
**Category:** Runtime / OS
**Status:** In Progress (contract only — no SQLite build yet)
**Master plan:** `doc/01_research/domain/simpleos_production_host_master_plan.md` §8 (durability contract) + §15 (Database production program — SQLite is the first DB milestone)
**Model:** `src/os/port/sqlite/sqlite_vfs_contract.spl`
**Spec:** `test/01_unit/os/port/sqlite_vfs_contract_spec.spl`
**Depends on:** `doc/02_requirements/os/posix_profiles.md` (P5 matrix: flock, mmap, shm), lane T2-C (honest flock)

## Overview

Master plan §15 makes "port SQLite over a proper SimpleOS VFS" the first
database milestone because a real `sqlite3_vfs` / `sqlite3_io_methods`
implementation stress-tests file locking, shm, mmap, fsync, atomic rename, WAL,
checkpoints and crash recovery — the exact §8 durability contract. The full
port is multi-session and needs the C toolchain (SQLite amalgamation). This
increment defines the SimpleOS-side shim **contract** as a pure-Simple model +
spec so the port has a typed target and an honest per-method status driven by
the real POSIX matrix.

**Honest-failure rule (mirrors Lane P5 / T2-C):** a facility that is absent is
reported `unsupported` here — never fake-supported. Shared mmap is absent by
design, so `xShmMap` fails closed, which is exactly what gates WAL mode off.

## Method contract table

SQLite VFS/IO method → SimpleOS facility → status. Status is
`supported | partial | unsupported`, driven by the facility statuses in the
model (`posix_flock_status`, `posix_mmap_shared_status`, `block_flush_status`).

| SQLite method | SimpleOS facility | Status | Note |
|---|---|---|---|
| xOpen | VFS `open(path, flags)` | supported | O_CREAT/O_EXCL via FileFlags |
| xClose | VFS `close(handle)` | supported | direct |
| xRead | VFS `seek` + `read` | supported | short read → SQLITE_IOERR_SHORT_READ |
| xWrite | VFS `seek` + `write` | supported | direct |
| xTruncate | VFS truncate — **absent in FsDriver trait** | unsupported | blocks `journal_mode=TRUNCATE` only; DELETE mode uses xDelete and is unaffected |
| xSync | block flush / fsync + §8 ordering guarantee | partial | flush exists; full ordering/FUA/dir-fsync/torn-write/power-loss recovery unproven |
| xFileSize | VFS `stat(path).size` | supported | |
| xLock | flock `LOCK_SH` / `LOCK_EX` | partial | advisory only; no blocking (conflict → EWOULDBLOCK); whole-file, no byte ranges |
| xUnlock | flock `LOCK_UN` / downgrade | partial | EX→SH downgrade is release+reacquire, not atomic |
| xCheckReservedLock | flock in-process holder query | partial | RESERVED not distinguishable from SHARED at whole-file layer |
| xFileControl | opcode passthrough (SQLITE_FCNTL_*) | partial | subset handled; unknown → SQLITE_NOTFOUND |
| xSectorSize | block layer `sector_size` | supported | 512 |
| xDeviceCharacteristics | block durability flags (SQLITE_IOCAP_*) | partial | only sector size published; atomic/safe-append/sequential/powersafe bits = 0 (conservative) |
| xShmMap | shared mmap (MAP_SHARED / shm_open) — wal-index | unsupported | **absent by design, EOPNOTSUPP**; gates WAL |
| xShmLock | locks over shared wal-index region | unsupported | no shared region |
| xShmBarrier | barrier over shared wal-index region | unsupported | no shared region |
| xShmUnmap | unmap shared wal-index region | unsupported | no shared region |

**Tally:** supported 6, partial 6, unsupported 5 (17 methods modeled).

## SQLite file-lock ladder → flock mapping

SimpleOS advisory locking is BSD `flock()` (whole-file, Lane T2-C). SQLite's
ladder maps as:

| SQLite lock level | flock op | exact? |
|---|---|---|
| NONE | LOCK_UN | yes |
| SHARED | LOCK_SH | yes |
| RESERVED | LOCK_SH | **no** — byte-range reserved intent not representable whole-file; tracked in-process |
| PENDING | LOCK_EX | **no** — pending byte not representable whole-file |
| EXCLUSIVE | LOCK_EX | yes |

Whole-file flock cannot express SQLite's separate RESERVED/PENDING bytes, so
those collapse onto SH/EX. This is honest and documented, not hidden.

## Durability contract SQLite relies on (§8)

The block+VFS layer must publish: sector / atomic-write assumptions, flush/FUA,
data-vs-metadata ordering, rename durability, dir fsync, torn-write detection,
cache volatility, TRIM, checksums, power-loss recovery. Current published
`BlockDurabilityFlags`: `sector_size=512`, `has_flush=true`; **all of**
atomic-write, safe-append, sequential, powersafe-overwrite = `false` (unproven,
so reported false — SQLite then behaves conservatively). Until §8's ordering /
torn-write / power-loss gates are proven, `xSync` stays `partial` and the
crash-recovery test list in §15 cannot be claimed passed.

## Supported vs blocked SQLite modes

- **Rollback journal (DELETE, default): SUPPORTED.** Critical path
  (open/close/read/write/sync/fileSize/lock/unlock/checkReservedLock/sectorSize)
  has no `unsupported` method. `xSync`/`xLock` are `partial`, so functional
  today with the §8 durability-proof caveat. Does not need `xTruncate` (journal
  removed via `xDelete`) or shm.
- **WAL mode: BLOCKED.** Requires the cross-process `-wal-index` via shared
  memory (`xShmMap`/`xShmLock`/`xShmBarrier`). **Exact prerequisite:** shared
  mmap (`MAP_SHARED` / `shm_open`) — POSIX Profile C facility, currently absent
  by design (fails closed EOPNOTSUPP, posix_profiles P5). Reporting `xShmMap`
  supported would let WAL corrupt, so it fails closed and WAL is gated off.

## Acceptance (spec oracles)

`test/01_unit/os/port/sqlite_vfs_contract_spec.spl` — 24 examples, 0 failures:
lock ladder maps correctly; `xShmMap` reports unsupported (fail-closed) so
`wal_mode_supported()` is false; `rollback_journal_mode_supported()` is true;
durability-flag query returns the published block-layer characteristics; status
tally is 6/6/5. Falsifying `xShmMap` to supported makes the WAL-gating test fail
(honest-failure wiring verified), then restore.
