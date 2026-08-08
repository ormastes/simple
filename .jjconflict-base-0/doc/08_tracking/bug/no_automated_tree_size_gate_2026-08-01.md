# No automated tree-size gate: `main` wiped twice with every guard green

- **ID:** `no_automated_tree_size_gate_2026-08-01`
- **Status:** FIXED — `scripts/check/check-tree-size-push.shs`, wired into the
  pre-push hook.
- **Severity:** critical (total loss of `main` content, twice in 24 hours)
- **Date:** 2026-08-01

## Symptom

`main` was reduced to near-zero files twice inside 24 hours. `118c636ead8` took
the tree from 109,375 files to 4. Every pre-push guard passed both times. The
only thing that ever caught a wipe was a human running

```
git ls-tree -r --name-only $C | wc -l
```

and noticing the number.

A second, subtler corruption appeared in the same window: a tree of **109,815
files — HIGHER than the healthy 109,543** — because `src/` listed the `lib`
entry TWICE (same mode, same sha, which git's tree format forbids) while seven
other `src/` subdirectories were missing entirely, including all 185 files of
`src/runtime`. `src/` held 9 entries instead of 15. A floor-only size check is
blind to that shape; so is every guard that existed.

## Root cause of the blind spot

The two pre-push guards recognise exactly two hazards:

- `check-no-conflict-tree-push.shs` — a tree whose entries are `.jjconflict*`.
- `check-no-conflict-markers-push.shs` — literal conflict-marker text in file
  content.

A tree truncated for any OTHER reason passes both. Two such reasons are on the
record: a git index truncated by ENOSPC, and an API `base_tree` landing that
silently inherited an already-wiped base. `5f1b96ad9a8` hardened both guards
against three proved fail-opens and recorded this as still open:

> no automated tree-size gate — both wipes would have been caught by one.

## Fix

`scripts/check/check-tree-size-push.shs`. Four independent fail-closed checks,
run over every commit in the outgoing range:

1. **Size band.** Relative to the base the push replaces (`+-0.15%`, i.e. `+-164`
   files at 109,557) **and** an absolute floor/ceiling (90,000 / 150,000). The
   absolute band is not redundant: when the base is ITSELF already wiped the
   delta is zero and only the floor can fire. Both wipes propagated exactly that
   way.
2. **Duplicate tree entries.** No path may appear twice in the recursive
   listing; two identical tree entries expand to two identical path lists, which
   exposes the corruption at any depth. `git fsck` is authoritative but takes
   >2 minutes on this repo, so it is for investigation, not gating.
3. **`src/` entry band** (13..25; measured 15, corruption showed 9). The single
   strongest signal: one cheap call, and it fired on the real case.
4. **Load-bearing path floors.** `src/runtime >= 150` (measured 185, corruption
   showed 0 — a proven canary), `src/os >= 1200`, `src/lib >= 5000`,
   `src/compiler >= 1200`, `src/app >= 2000`, `scripts >= 500`, `doc >= 1000`.
   `src/std` is deliberately NOT a canary: it holds ONE file, so a non-empty
   test on it is vacuous.

### How the band was derived

Measured across the 30 commits ending at `502af609d9a5`: tree size 109,539 ..
109,564; per-commit churn +1/+2/+4 typical, largest single move -25 (a
legitimate dead-package deletion). Corruption deltas for separation: the wipe
was -109,371, the duplicate-entry corruption was +272. A tolerance of 0.15%
(+-164) sits ~6.5x above the largest real churn and ~40% below the corruption
delta, separating both hazards from normal work with room on both sides.

A lane that legitimately moves more than the band allows states its expected
post-count with `--expect-files <n>`, which recentres the band on the stated
number and prints it in the verdict — it RECORDS the expectation rather than
bypassing anything. Every other check still applies. PROVED: `--expect-files
109372` on the missing-`src/runtime` fixture still FAILS on the canary. There is
no flag that turns a check off and no environment variable overrides a
threshold.

## Contract

Matches `check-no-conflict-tree-push.shs` as amended in `5f1b96ad9a8`: verdict
always on stdout, always first-word-tagged `PASS` / `FAIL` / `ERROR`;
`PASS — <n> commit(s) checked` with n always > 0; `ERROR — nothing was checked`
(exit 2) whenever the guard could not do its job, including cwd outside a git
repo; no `git` exit status discarded; nothing load-bearing read through a pipe;
`/usr/bin/grep` pinned because the interactive default here is ugrep.

## Wiring

`scripts/check/pre-push-conflict-tree-guard.shs` (the installed
`.git/hooks/pre-push`) now runs three guards on every ref instead of two.
Install:

```
ln -sf ../../scripts/check/pre-push-conflict-tree-guard.shs .git/hooks/pre-push
```

## Non-vacuity evidence (all PROVED)

`--selftest` runs before every scan and is FATAL: 14 fixtures, 11 must-fail and
3 must-pass, each isolating one check.

**Sabotage matrix** — each check neutered in turn; the selftest must then FAIL
rather than pass quietly. All eight caught:

| sabotage | selftest exit | fixture that caught it |
|---|---|---|
| duplicate check | 2 | `duplicate-entry`, `duplicate-vs-base` |
| `src/` entry band | 2 | `src-entries-shrunk` |
| load-bearing floors | 2 | `missing-src-runtime` |
| absolute floor | 2 | `absolute-floor-only` |
| absolute ceiling | 2 | `oversize-absolute` |
| relative band | 2 | `band-jump` |
| `evaluate_commit` always clean | 2 | all 11 must-fail |
| assertion harness made vacuous | 2 | all 11 must-fail |

The absolute-floor sabotage initially passed GREEN — no fixture isolated it,
because the truncated fixtures also tripped the canaries. The
`absolute-floor-only` fixture (20 files, but `src/` entries and both canaries
healthy) was added for exactly that gap. This is the gap the sabotage step
exists to find, and it found one.

**Real fixtures against the real 109k-file tree**, built on `502af609d9a5`:

| fixture | files | `src/` entries | `src/runtime` | guard |
|---|---|---|---|---|
| truncated (`.jjconflict-*` only) | 3 | 0 | 0 | exit 1 |
| duplicate `src/lib`, 7 dirs gone | 114,624 | 9 | 0 | exit 1 |
| `src/runtime` removed | 109,372 | 14 | 0 | exit 1 |
| healthy (+1 file) | 109,558 | 15 | 185 | exit 0, PASS |

**Real `git push` through the real hook** (bare remote, `.git/hooks/pre-push`
installed, not the script invoked by hand): truncated BLOCKED, duplicate-entry
BLOCKED, missing-`src/runtime` BLOCKED, healthy PUSHED. The duplicate-entry
fixture was blocked by the tree-size guard ALONE — both conflict guards passed
it, which is the motivating gap made concrete.

**cwd fail-closed**: run from a `git archive` worktree under `/dev/shm` with no
`.git` — the exact environment that produced the previous fail-open — the guard
exits 2 with `ERROR — nothing was checked`, not 0.

**Empty range**: an explicitly supplied range resolving to 0 commits is exit 2,
not a pass.

## Deliberate strictness

- A push whose net file delta exceeds 164 is refused unless the lane states the
  expected count. That is intended.
- A brand-new ref has no base, so only the absolute band applies; the verdict
  says so explicitly. That is a narrowing, not a fail-open — the absolute floor
  is the check that catches a wipe.
- If a threshold is genuinely wrong, edit it in the script TO THE NEWLY MEASURED
  BOUNDARY, in the same commit as the work. Do not relax it to make a run green.
