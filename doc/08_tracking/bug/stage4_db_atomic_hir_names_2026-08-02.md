# Stage4 atomic-database HIR names
## Resolved 2026-11-25 — HIR-names fix verified; Windows lock-read divergence fixed

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Reproduction

Stage4 HIR lowering stopped in `nogc_async_mut/db_atomic.spl` with unresolved
file, lock, process, time, and `_` names.

## Fix

Both no-GC database mirrors import file operations, process identity, and time
from their concrete owner modules. The async mirror now uses the same `?`
Result propagation as the sync implementation instead of matching `Ok(_)`,
which Stage4 treated as an unresolved identifier.

## Regression evidence

`db_atomic_hir_contract_spec.spl` checks concrete owners, removal of the broad
facade import, native-safe propagation, and sync/async mirror parity.


## Verification 2026-11-25 (work/p3-bao-20261125)

HIR-names fix confirmed by inspection on current source: both mirrors import
file ops, process identity, and time from concrete owner modules
(`std.nogc_sync_mut.io.{file_ops,sysinfo_ops,time_ops}`,
`src/lib/nogc_sync_mut/db_atomic.spl:25-27`; async mirror same shape), no
broad facade import remains, and lock acquisition uses `?` Result propagation
(`db_atomic.spl:161,204`).

However the named regression evidence `test/01_unit/lib/db_atomic_hir_contract_spec.spl`
was RED on this Windows host (2 of 4 examples failing, both `atomic_update`
rows: read-back content was empty). Root cause was a NEW, separate defect, not
the HIR issue: `FileLock.acquire` locked the DATA file, and on Windows
`LockFileEx` is a mandatory byte-range lock, so the `file_read` inside
`atomic_update` failed with `ERROR_LOCK_VIOLATION` and silently yielded `""`
(isolated with a minimal probe: `file_read` under a held `file_lock` returns
empty on Windows, content on Unix). Fix: `FileLock.acquire` in both mirrors
now locks the sidecar `path + ".lock"` instead of the data file, preserving
mutual exclusion among all db_atomic operations while leaving the data file
readable under the lock. After evidence: the contract spec is 4/4 green, and
`db_atomic_mirror_result_parity_spec.spl` (5/5),
`db_atomic_ok_wildcard_arm_spec.spl` (4/4), and
`db_atomic_table_headers_rows_spec.spl` (6/6) all pass. Verified with
`SIMPLE_LIB=src bin/simple.exe test <spec> --mode=interpreter` (pinned
tracked binary, worktree base fcd95d41d60).
