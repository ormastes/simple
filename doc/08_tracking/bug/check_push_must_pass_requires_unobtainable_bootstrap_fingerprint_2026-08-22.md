# check-push-must-pass requires a bootstrap fingerprint no tree can produce (2026-08-22)

**Status:** OPEN (blocks every push through the tracked pre-push dispatcher)
**Introduced by:** 09e879ff838 `fix(check): harden must-check ledger ownership`
**Hook chain:** `scripts/hooks/pre-push` -> `pre-push-conflict-tree-guard.shs` -> `exec check-push-must-pass.shs`

## Symptom

Pushing `326b7b4a03e` (a two-file orchestrator fix, rebased on origin tip) with
the tracked dispatcher (`git -c core.hooksPath=<tree>/scripts/hooks push ...`):

```
check-hook-installation: PASS — 10 check(s) performed, hook wiring intact
push-must-check: FAIL — ledger is malformed stale or has a non-passing push-blocking row
```

## Why it cannot pass

`check-push-must-pass.shs:152-157` reads `doc/08_tracking/check/must_check_db.sdn`
and `config/check/must_check_gates.sdn` out of the PUSHED commit, fingerprints
the pushed tree, and requires `source_fingerprint` to match AND every
push-blocking row to be `pass`. At origin/main the ledger is
`source_fingerprint: "unrecorded"` with 28 rows `todo, never` (compiler-stage1..4,
rules-full, engine-differential, ...). The only writer is
`check-bootstrap-must-pass.shs`, run by `bootstrap-from-scratch.sh --full-bootstrap --deploy`.

Phase 1 of the current hardening work is precisely obtaining a successful
full bootstrap: the stage1 parse phase is what `parse_shard_orphaned_claims_after_shard_death_2026-08-22.md`
fixes. The hook therefore blocks the fixes that are needed to produce the
evidence it demands -- a circular gate. `--no-verify` is the only way a
commit has landed since 09e879ff838, which means the other 57 guards the
dispatcher fans out to are ALSO skipped on every landing (the fail-open
shape of `fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md`).

## Secondary wiring defects seen on the same push

- Shared `.git/hooks/pre-push` symlinks to `/mnt/data/worktrees/codex-01a023a8/scripts/hooks/pre-push`
  (another session's tree); `check-hook-installation` FAILs on it, and
  `install-must-check-hooks.shs --install` refuses because a `pre-push.local` exists.
- `land.shs` pushes via `sj`, which segfaults in a plain `git worktree` (no `.jj`).

## Proposed fix

Make the must-check ledger gate ADVISORY (report, exit 0) until the ledger
has recorded one genuine PASS, or key the block on a ledger that is
*stale relative to a previous pass* rather than on "never recorded" --
the same promotion discipline used for `check-stage-binaries-runnable.shs`
and `check-no-unresolved-runtime-symbols.shs` (landed advisory while honestly
RED, promoted once green). Keep the structural guards mandatory; they must
not be skipped as collateral of an unobtainable gate.
