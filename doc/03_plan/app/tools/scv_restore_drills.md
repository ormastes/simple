# SCV Restore Drills (SCV-MIG-23)

Six disaster-recovery drills for the S4→S5 gate list (stabilization doc,
§restore tests). Run:

```bash
sh scripts/check/check-scv-restore-drills.shs            # all six
sh scripts/check/check-scv-restore-drills.shs --only corrupt-db
sh scripts/check/check-scv-restore-drills.shs --selftest # fatal fixtures only
sh scripts/scv-migration/steps/SCV-MIG-23.shs            # plan-step wrapper
```

Each drill runs in an isolated temp repo (a.txt + sub/b.txt, mirroring
SCV-MIG-14) and ends with the shared assessor: `scv doctor` PASS + `scv fsck`
"OK checked=". Verdict last line: `PASS — 6 drill(s) recovered, 0 failures`.

| Drill | Proves | Failure means |
|---|---|---|
| git-only | Losing all of `.scv` is cheap: re-init + snapshot from git alone; `verify-backends --git` byte-matches | SCV cannot be rebuilt from the Git authority — S2 promise broken |
| checkpoint-git | A saved `.scv/checkpoints` dir restored into a fresh store is healthy and tree-matches git | Checkpoints are not a usable restore medium |
| scv-objects-only | With `.git` deleted, `scv export-tree` reproduces the exact working bytes from SCV objects alone | SCV objects are not self-sufficient; data would be git-hostage |
| corrupt-db | Garbage in derived `status_index.sdn` is repaired by `scv rebuild-db`; fsck line unchanged | Derived DB corruption is not recoverable / touches real objects |
| missing-indexes | Deleted parser index/cache is non-fatal (doctor never FAIL) and rebuilt by `parse-index` + snapshot | A derived cache loss bricks doctor — rebuildable state treated as truth |
| interrupted-txn | Crash injection (`SCV_FAULT_AFTER=commit,head`) leaves an OLD-or-NEW repo; doctor/WAL recovery works | Torn transactions leave half states; see full sweep in `scripts/check/check-scv-crash-harness.shs` |

`--selftest` (always run first, fatal) corrupts a commit object with recovery
deliberately skipped and requires the same assessor to flag it, checks the
OLD-or-NEW classifier fixtures, and requires a 0-drill selection to ERROR.

Known nuance: `scv doctor` treats a *missing* parser index as vacuously OK
(`scv_validate_parser_index` returns clean when the file is absent), so the
missing-indexes drill asserts "never FAIL" rather than a literal STALE row.
