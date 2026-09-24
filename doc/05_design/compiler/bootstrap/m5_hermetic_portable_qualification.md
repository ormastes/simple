<!-- codex-design -->
# M5 Hermetic Portable Qualification Design

## Flow

1. Snapshot and re-execute the driver after a before/copy/after digest match.
2. Admit exactly three regular, non-symlink source files.
3. Write the ordered source inventory and copy each admitted byte stream.
4. Verify source and copied digests during every copy.
5. Make the snapshot read-only and verify an identical pre-run source inventory.
6. Run the snapshotted checker from the snapshot root with isolated `HOME`,
   `TMPDIR`, locale, and PATH.
7. Re-inventory source and snapshot; reject either drift before considering exit 0.
8. Bind stdout, stderr, all inventories, and the snapshot in `status.env`, then
   retain the complete evidence directory read-only.

## Receipt

`macos-m5-hermetic-portable-qualification-v1` records status, stable reason,
source/snapshot inventory digests, self-bootstrap digest, checker exit code,
all drift decisions, timestamps, and explicit `commit_attempted=false` and
`deploy_attempted=false` facts. The portable checker may exercise a pointer
only inside its isolated disposable fixture; that is not deployment.

## Failure Rules

Snapshot drift outranks checker failure because execution bytes are no longer
trustworthy. Source post-run drift outranks checker exit because the run cannot
be attributed to one worktree generation. Existing evidence directories are
never overwritten.

## Test Strategy

The shell mutation suite proves clean admission, exact closure exclusion,
pre-run source drift rejection, during-run source drift rejection, snapshot
drift rejection, driver-source drift rejection, and symlink rejection. The
canonical M5 portable checker must not run until this mutation suite passes.
