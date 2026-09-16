# push-must-check blocks every push: must_check ledger id-set drifted from the gate manifest (2026-09-01)

## Verdict (before)

```
$ MUST_CHECK_ROOT=<repo> sh scripts/check/check-push-must-pass.shs --from-pre-push-hook < refs.txt
push-must-check: FAIL — ledger is malformed stale or has a non-passing push-blocking row
EXIT=1
```

(`refs.txt` is one normal pre-push row: `refs/heads/main <origin/main> refs/heads/main <origin/main~1>`.)
Run bare from a shell with no stdin the script instead says
`FAIL — no pushed refs were provided outside the pre-push hook` — a DIFFERENT
failure path, which is why this was mis-triaged.

## The mechanism is NOT "every ledger row is todo"

An all-`todo` ledger is the DESIGNED steady state and is explicitly excused.
`ledger_is_unpromoted_at_rev` sets `ALLOW_UNPROMOTED_LEDGER=1` when the
PREDECESSOR revision's ledger has `source_fingerprint: "unrecorded"` and zero
`pass` rows — which is exactly origin/main's state — and that flag suppresses
both the fingerprint-staleness check (11) and the blocking-row check (21).
So `todo`/`never` rows alone never block a push.

## The real mechanism: check 15, id-set equality

`validate_ledger_text` requires the sorted set of `bootstrap`-tier ids in
`config/check/must_check_gates.sdn` to equal the sorted set of row ids in
`doc/08_tracking/check/must_check_db.sdn`. Measured at origin/main:

- manifest bootstrap gates: **50**
- ledger rows: **31**
- in manifest but not ledger: **21** (`c-runtime-compiles`, `no-direct-rt`,
  `guard-wiring`, `perf-regression-tests`, `use-target-resolves`,
  `outline-parse-terminates`, `process-wait-eintr-retry`,
  `signature-type-import-provenance`, `runtime-api-regression-selftest`,
  `interpreter-module-owners-selftest`,
  `interpreter-extern-registry-gap-selftest`,
  `type-walk-constructor-parity-selftest`, `raw-sffi-unsafe-ratchet`,
  `native-array-element-type`, `stage4-tooling-matrix`,
  `web-server-request-port`, `db-server-request-port`,
  `caret-agent-runtime-primitives`, `caret-batch-process-adapter`,
  `caret-messaging-primitives`, `caret-production-multi-manager-launch`)
- in ledger but not manifest: **2** (`caret-agent-manager-primitives`,
  `caret-multi-manager-launch` — the pre-rename names of two caret gates)

The script's hardcoded `REQUIRED_BOOTSTRAP_IDS` at origin/main matches the
manifest exactly (50 = 50), so the script is NOT misreading a valid ledger.
The ledger is genuinely stale.

## Systemic cause

Only a full successful bootstrap run of
`scripts/check/check-bootstrap-must-pass.shs` regenerates the ledger. Anyone
who ADDS or RENAMES a gate row in `config/check/must_check_gates.sdn` therefore
lands a repo-wide push blocker, because the ledger cannot be refreshed without
a bootstrap that is itself currently blocked. There is no cheap
"resynchronise the ledger id set" path.

Note also that a stale local checkout stays blocked even after this fix: the
working-tree copy of `check-push-must-pass.shs` in one shared worktree carries
an older 39-entry `REQUIRED_BOOTSTRAP_IDS` including the two pre-rename caret
ids, so it fails check 16 against the current manifest. Rebasing is required.

## This is the third guard being routed around

This session was already authorised to use `--no-verify` for two known hook
bugs (`OLDGUARD_DEPTH exceeds cap` recursion; the tree-size band). This ledger
drift is a third, and it blocks EVERY push repo-wide rather than a class of
pushes. A guard that every pusher routes around protects nothing: while this
was red, none of the push-tier gates behind it (conflict-tree, conflict-markers,
tree-size, rules-quick, c-runtime-compiles, no-direct-rt, ...) ran at all,
because `run_manifest_push_gates` is reached only AFTER ledger validation.

## Fix

Regenerate `doc/08_tracking/check/must_check_db.sdn` from the manifest: one
`todo, never` row per bootstrap gate, owner from the generator's `gate_owner`
mapping, `unblock_condition` from the manifest description, command copied
byte-for-byte from the manifest (check 26 requires equality). Nothing is
weakened: every gate stays visible debt at `todo`, no row is promoted to
`pass`, and the `source_fingerprint` stays `unrecorded` so a real bootstrap
still has to promote them.

## Verdict (after)

```
push-must-check: PASS — lightweight committed-tree and bootstrap-ledger checks passed
```
(or, if a push-tier gate is independently red, the failure moves to
`push-must-check: BLOCKING gate <id> failed` — which is the ledger check
working and the gates finally running.)

## Measured after-verdict, and the NEXT blocker (not fixed here)

With the ledger resynced, ledger validation passes and the run proceeds into
`run_manifest_push_gates` for the first time. It then stops at a DIFFERENT,
independent bug:

```
check-no-conflict-tree-push: ERROR — unknown option '--rev-list-args-or-tips'; raw mode is '--rev-list-args <args>...'
push-must-check: BLOCKING gate push-conflict-tree failed (exit 2)
push-must-check: FAIL — outgoing commit union contains a conflict tree or exceeds its bounded history limit
```

That is the ledger fix working: the failure moved from validation into the
gates. The remaining defect is a caller/callee option mismatch —
`check-push-must-pass.shs:354` (`run_conflict_tree_union`) passes
`--rev-list-args-or-tips`, but `check-no-conflict-tree-push.shs` at origin/main
only accepts `--rev-list-args`. Invoked directly with a bare range the same
guard PASSes (`1 commit(s) checked ... 0 conflict trees`), so the guard itself
is sound; only the union call path is broken.

**Deliberately not fixed here.** Another session already owns it: agent
worktrees under `.claude/worktrees/` carry a
`check-no-conflict-tree-push.shs` that implements `--rev-list-args-or-tips`
(with a `--` separator and fallback tips), and
`doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`
names `--rev-list-args-or-tips` and `--push-tip` as known caller/callee option
mismatches. Landing a competing fix would clobber that work.
