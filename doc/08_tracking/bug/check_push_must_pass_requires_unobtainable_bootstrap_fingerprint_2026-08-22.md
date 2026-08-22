# check-push-must-pass requires a bootstrap fingerprint no tree can produce (2026-08-22)

**Status:** RESOLVED — primary Codex must-check lane
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

- The shared-worktree absolute-hook defect is resolved separately in
  `shared_worktree_pre_push_absolute_symlink_2026-08-22.md`; it does not resolve
  this ledger-fingerprint bootstrap cycle.
- `land.shs` pushes via `sj`, which segfaults in a plain `git worktree` (no `.jj`).

## Required fix

Treat the canonical all-TODO `source_fingerprint=unrecorded` ledger as an
unpromoted baseline, not as PASS. While both the pushed revision and its remote
predecessor are unpromoted, report the debt and continue into every structural
push gate. Once a predecessor contains genuine bootstrap-produced state, reject
any attempted downgrade to `unrecorded`; normal fingerprint, evidence, and
push-blocking validation remains fail-closed. Keep the structural guards
mandatory in both states so missing bootstrap evidence cannot disable them.

## Resolution evidence

The focused fixture proves both sides of the ratchet: an unpromoted predecessor
accepts an all-TODO ledger and still invokes structural gates; after genuine
bootstrap-produced PASS evidence, a reset to `unrecorded` is rejected. The
complete contract passed with `selftest=5s`, `ref-path=0s`, `two-ref=0s`, and
`installed-hook=0s` at 59,136 KiB peak RSS.
The representative committed-tree path then ran all five real production gates
on the 118,074-file repository in 5.40s at 211,932 KiB peak RSS.
