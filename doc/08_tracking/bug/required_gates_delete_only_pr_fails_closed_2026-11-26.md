# Required gates fail closed on a delete-only PR (2026-11-26)

**Status:** open
**Severity:** P2. It blocks legitimate debt-cleanup PRs from landing on the required check.
**Found by:** repo-hygiene triage lane, PR #11828 (base `release/1.0.0`).

## Symptom

A PR whose only changes are file deletions fails the required check
`Code Idiom & Structural Ratchet Gates` (`fast-gates` job), even though deleting
an unreferenced file is a legitimate change.

Run: https://github.com/ormastes/simple/actions/runs/45708766974/job/139537435987

Exact failure lines (range `1ca52709fb84805ce4b2eddf04084f7a113dde05..4b6b797a1fdb32c1b4f291d8e57477a90c8f9557`):

```
local-rust-duplicate-reexport fail
local-range-shs-hygiene fail
FAIL — 94 row(s) checked, 2 failed: local-rust-duplicate-reexport local-range-shs-hygiene
--- row local-rust-duplicate-reexport log ---
selftest: 12 fixtures passed
ERROR — nothing was checked (empty AMRC range lacks distinct tree-equivalent history: 1ca52709fb84805ce4b2eddf04084f7a113dde05..4b6b797a1fdb32c1b4f291d8e57477a90c8f9557)
--- row local-range-shs-hygiene log ---
selftest: 17 fixtures passed
ERROR — nothing was checked (empty AMRC range lacks distinct tree-equivalent history: 1ca52709fb84805ce4b2eddf04084f7a113dde05..4b6b797a1fdb32c1b4f291d8e57477a90c8f9557)
```

## Gates

- `scripts/check/check-rust-duplicate-reexport.shs` (line ~181)
- `scripts/check/check-range-shs-hygiene-push.shs` (line ~181)

Both run `git diff --name-status --diff-filter=AMRC <merge-base> <tip>`. A
delete-only range yields an empty AMRC set. The empty-set path then passes only
when the base and tip trees are *identical*, which is false whenever something
was deleted. Otherwise it returns `ERROR — nothing was checked` (exit 2).

## Why this is a gate bug

On a delete-only range there is nothing for either gate to check. A deletion
cannot add a duplicate Rust re-export, and it cannot add or break a `.shs`
script. Treating the case as "could not determine" is wrong. A real "nothing
changed" range (identical trees) is already handled. The missing case is a
range that is non-empty and has only `D` entries.

## Expected fix (do not weaken the vacuity guard)

When the AMRC set is empty, check the full `--name-status` set as well. If it
has one or more entries and all of them are `D`, emit a non-vacuous PASS that
states the count, for example `PASS — <n> deletion(s) verified, no added or
modified files to scan`. Any other empty case must still be ERROR. Add a
selftest fixture for each gate: a delete-only range must PASS, and an empty or
missing range must still ERROR.

## Workaround used

PR #11828 carries this bug record and the debt record, so its range is no longer
delete-only. The gates were not changed.
