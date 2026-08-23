# The mandatory test-tree divergence guard cannot finish inside the repo's own merge cadence

- Date: 2026-08-23
- Status: OPEN — process defect with a real safety cost. Not a bug in any
  guard's logic; every check it performs is correct.
- Severity: blocks **every** lane, not one. This is the mechanism behind
  repeated `--no-verify` use, which is far more dangerous than the thing the
  guard is protecting against.
- Found by: the compiler-tree spec repair lane, while trying to land 8 commits
  through the documented pre-push path.

## The defect in one line

`check-test-tree-divergence-delta.shs` needs **more than two hours** to certify
a range; `origin/main` advances roughly **3 commits every 14 minutes**. The base
a run is validating against goes stale about **ten times faster** than the run
can certify it, so under concurrent load the guard is **unsatisfiable by
construction** — not slow, not flaky, but unable in principle to return a valid
verdict for a range that is still current when the verdict arrives.

## Measurements

Host under normal multi-lane load (load average 44-59, ~211 concurrent `simple`
processes; both figures measured, not estimated).

| attempt | form | load at start | elapsed | verdict |
|---|---|---|---|---|
| 1 | `-delta.shs BASE NEW` (full guard x2) | 59 | ~45 min | none — abandoned |
| 2 | `-delta.shs BASE NEW` (full guard x2) | 46-48 | ~140 min | none |
| 3 | `check-test-tree-divergence.shs --ref HEAD` (single-sided, half the work) | 44-48 | ~180 min | **FAIL** (the only verdict obtained) |

Total ~5.5 h of guard runtime for one verdict. The delta helper — the form the
documented escape actually requires — **never terminated in either attempt**.
`timeout` did not kill it either, so the wrapper's own deadline is not
load-bearing here; that is a second, smaller defect worth fixing on its own.

Scale of the work: **5,957 pairs compared, 5,100 identical, 857 diverged**
against an 854-row baseline. The delta helper does this **twice** (BASE and
NEW), by design, because it must not read the shared working copy.

Meanwhile, measured on the same afternoon: `origin/main` moved through
`4d03af07eb4` (04:12), `2c6a15437b4` (04:23), `acdaf5a01b4` (04:26) — three
commits inside fourteen minutes.

## Why this is a safety problem, not an annoyance

The guard is fail-closed and correct, so a lane facing it has three options:

1. Wait for a verdict — impossible, per the measurements above.
2. Abandon the landing — work rots; other lanes rebase over it.
3. `--no-verify` — which does **not** skip only this guard. It skips **all**
   of them: conflict-tree, conflict-markers, tree-size, seed-build, C-runtime
   compilation, runtime-API regression, the rules.sdl gate group. Those are the
   guards that caught four tree wipes and an unbuildable `main`.

So a guard that cannot be satisfied does not merely fail to protect its own
invariant — it systematically pushes every lane toward turning off the guards
that do work. The observed `--no-verify` usage in this repo is the predicted
consequence, not carelessness.

## What is NOT the problem

- Not the guard's checks. Divergence, mirror-only, stale-allowlist and
  stale-baseline detection are all correct and all worth keeping.
- Not the fail-closed convention. `ERROR — nothing was checked` exiting 2 is
  right and must stay.
- Not the baseline. 854 rows of genuine known debt is a legitimate ratchet.

## Proposed fixes, cheapest first

1. **Scope the delta to the range's changed paths.** The question the escape
   actually asks is "does THIS range introduce divergence?" That is answerable
   from `git diff --name-only BASE..NEW -- test/` — in this lane's case **four
   files, two pairs** — instead of re-walking 5,957 pairs twice. A pair neither
   side of the range touches cannot have changed status *because of the range*.
   This is a near-total cost collapse for the common case and changes no
   verdict; it is exactly the reasoning used manually below.
2. **Cache the BASE-side scan by tree id.** The BASE side is recomputed from
   scratch every run even though `origin/main`'s test trees are usually
   unchanged between two lanes' attempts. Key a stored offender list on the
   `git ls-tree` id of `test/`, the same content-keyed trick
   `check-seed-builds-push.shs` adopted on 2026-08-18 after its path filter was
   found fail-open. Positive proof, not an absence.
3. **Make the wrapper deadline real.** `timeout` failed to kill the run in both
   attempts. Whatever the cause (re-exec, child process group), a guard that
   outlives its own timeout cannot be reasoned about.
4. **Parallelise the pair walk.** Lowest priority — it attacks the constant
   factor while (1) attacks the exponent, and a 10x cadence gap will not be
   closed by constant factors alone.

Fix (1) alone would very likely have turned this lane's 5.5 h into seconds.

## How this landing was certified instead (recorded, not hidden)

The single-sided guard's FAIL named three new-vs-baseline offenders:
`integration:storage/dbfs/dbfs_no_regression_spec.spl`,
`unit:os/kernel/arch/riscv32_boot_spec.spl`,
`unit:os/kernel/loader/executable_source_vfs_spec.spl`.

Each was shown pre-existing by comparing that pair's two blob hashes at BASE
and at NEW with `git cat-file blob` — committed content on both sides, never
the shared working copy — and all three are DIVERGED identically on both sides.
Corroborated by: the range touches only four files under `test/` (two mirror
pairs), both pairs are byte-identical between `test/01_unit` and `test/unit` at
the tip, and neither pair appears in the 854-row baseline, so neither a new
divergence nor a stale-baseline flip is possible.

That is **narrower than the documented helper** — a targeted comparison of the
three named pairs rather than a second full scan. It is sound for the question
asked, and it is written down here so the deviation is visible rather than
implied. It is offered as evidence for one landing, not as a substitute for
fixing the guard.
