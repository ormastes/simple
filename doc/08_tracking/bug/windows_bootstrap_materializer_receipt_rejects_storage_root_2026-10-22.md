# Windows bootstrap receipt rejected under centralized in-repo storage (2026-10-22)

## Symptom

`scripts/bootstrap/bootstrap-from-scratch.sh` aborted during startup on
Windows (Git Bash) with:

```
materialize-symlinks-windows: receipt must use the dedicated bootstrap output root
VERDICT — ABORTED: stage=starting exit=1
```

No stage started; the abort happened before any compiler work.

## Root cause

The receipt-path policy in
`scripts/setup/materialize-symlinks-windows.shs` only accepted receipts under
`$repo_root/build/bootstrap`, `/tmp`, `/var/tmp`, or absolute paths outside
the repo root. With the default centralized storage layout,
`SIMPLE_WORKTREE_STORAGE_ROOT=<repo>/.simple/storage` (see
`scripts/lib/storage-roots.shs`), the canonical bootstrap output root is
`<repo>/.simple/storage/build/bootstrap`. The startup materializer
(`scripts/bootstrap/bootstrap-materialized-startup.shs`) writes its receipt
under that output root, which matched the `"$repo_root"/*)` reject arm.

The policy predated the centralized-storage default and never learned the
dedicated storage-root output location.

## Fix

- `materialize-symlinks-windows.shs` gains an explicit
  `--allow-receipt-root PATH` option (repeatable) checked ahead of the
  repo-root reject arm; unknown/relative roots are refused.
- `bootstrap-materialized-startup.shs` passes
  `--allow-receipt-root "$bms_output"` so the receipt stays in the same
  dedicated output root the bootstrap itself selected.

No policy strength was reduced: the repo-root reject arm still applies to any
receipt path not explicitly authorized.

## Evidence

- Reproduced on `release_phase3` (HEAD `4d058f7c73e`), 2026-10-22:
  `sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap
  --stop-after-stage2` → ABORTED at stage=starting.
- After the fix the same command passes materialization and proceeds into
  Stage 1/2 work.
