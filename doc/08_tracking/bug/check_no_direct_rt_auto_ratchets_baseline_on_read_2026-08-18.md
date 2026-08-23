# `check-no-direct-rt.shs` rewrites its tracked baseline as a side effect of merely running

- **Status:** **REOPENED 2026-08-23** — the auto-write path is still live in
  `scripts/check/check-no-direct-rt.shs:224` and fired twice in one session. See
  § Regression 2026-08-23 at the end of this record.
- Previous status: RESOLVED 2026-08-18 (fix + selftest fixtures landed same day)
- **Date:** 2026-08-18
- **Area:** `scripts/check/check-no-direct-rt.shs`, `scripts/check/no_direct_rt_baseline.txt`
- **Severity:** Medium (a gate that records unreviewed numbers; also makes every
  "read-only" audit dirty the working tree)
- **Found while:** binary_runtime_hardening lane, scoping goal 1 (remove direct `rt_*`).

## Summary

The gate is documented and used as a check, but it **writes tracked repository
state on the success path**:

```sh
if [ "$forbidden" -lt "$baseline" ]; then
  echo "$forbidden" > "$BASELINE_FILE"
fi
```
(`scripts/check/check-no-direct-rt.shs`, baseline-ratchet block)

So any invocation — including one whose only purpose is to *read* the current
count, e.g. an audit agent or a developer sanity-checking before a push —
silently commits a new ratchet floor. Nobody reviews that number; it is
recorded by whoever happened to run the script last.

## Observed

A read-only inventory pass in this lane ran the gate once. That single run
changed tracked content:

```
$ git status --porcelain scripts/check/
 M scripts/check/no_direct_rt_baseline.txt
```

with the file going `19362` -> `18788`. No `.spl` file was edited by that pass;
the entire 574-count delta was pre-existing reality that the recorded baseline
had simply drifted away from.

## Why this matters

1. **The ratchet floor is set by accident, not by review.** The plan
   (`doc/03_plan/infra/binary_runtime_hardening/plan.md`, "Warning->error
   phases", phase B: "baseline only ratchets down") wants the floor to move
   when work lands. Here it moves when anyone *looks*.
2. **It hides how stale the recorded number was.** Three places disagreed at
   the time of writing — the baseline file (`19362`), `CLAUDE.md` (`12948`),
   and the plan's own gate table (`12794`). A self-rewriting baseline makes
   that drift invisible: the next run just quietly agrees with itself.
3. **"Read-only" audits are not read-only**, so an audit in a shared worktree
   can be mistaken for someone's uncommitted work, or be clobbered by a sync.

## Suggested fix

Separate measuring from recording. Keep the comparison, drop the implicit
write; move the write behind an explicit flag:

- default run: compare against the baseline, print measured counts, never write;
- `--update-baseline`: the only path that rewrites the file, intended to be run
  deliberately by whoever lands a reduction and to be reviewed in that commit.

A FAIL is unaffected. A run that finds `forbidden < baseline` should still PASS,
but say so — e.g. `PASS — ... forbidden=18788 (baseline 19362; 574 below floor,
run --update-baseline to record)` — rather than silently ratcheting.

## RESOLVED — 2026-08-18

`scripts/check/check-no-direct-rt.shs` now separates measuring from recording,
exactly as proposed above. Every write of `$BASELINE_FILE` — both the
below-floor path and the missing-baseline path — is gated behind a new
`--update-baseline` flag. The default run never writes.

Unchanged by design: FAIL when forbidden > baseline (exit 1), ERROR when
`scanned == 0` (exit 2), `--critical`, `--selftest-only`, the
verdict-is-last-stdout-line contract, and the fix-it guidance printed before
the verdict.

The fatal selftest went 3 -> 5 fixtures. The two new ones invoke the script as
a child process against a throwaway tree (baseline `9` vs a measured `1`):
fixture 4 asserts a passing run leaves the baseline file byte-identical AND
mtime-identical and that the verdict names the delta; fixture 5 asserts
`--update-baseline` does rewrite it.

Verified independently by the parent session, not merely reported:

```
BEFORE: 18788 | git: []
  forbidden_product: 18566
PASS — 14829 file(s) scanned, forbidden=18566 (baseline 18788; 222 below floor, run --update-baseline to record)
AFTER:  18788 | git: []
```

`PASS — 5 selftest fixture(s) checked` for `--selftest-only`.

Corroborating evidence for why this mattered: during the fix the measured
`forbidden` count moved 18788 -> 18566 *between two runs*, because a parallel
agent was editing `.spl` files in the same shared worktree. Under the old
behaviour that transient number would have been silently written to the
tracked baseline by whichever run happened to observe it.

Note the recorded baseline is deliberately left at 18788 rather than ratcheted
to 18566: the 222 delta is an allowlist reclassification
(`doc/08_tracking/rt_boundary/provider_classification_2026-08-18.md`), which
HIDES call sites rather than removing them, and recording it silently is the
class of thing this bug was about. See also
`doc/08_tracking/bug/check_no_direct_rt_counts_extern_declarations_as_call_sites_2026-08-18.md`
— the count itself is still inflated by `extern fn rt_*` declarations.

## Regression 2026-08-23 — still writes on the success path, now via the push hook

Marked RESOLVED on 2026-08-18, but the downward-ratchet write survives verbatim:

```sh
# scripts/check/check-no-direct-rt.shs:222-224
if [ "$forbidden" -lt "$baseline" ]; then
  echo "$forbidden" > "$BASELINE_FILE"
fi
```

(a second, defensible write at `:203` records a baseline when the file is absent.)

Observed twice in a single session in `/mnt/fast/wt/rt-build-1`, on a tree whose
changes touched no `.spl` at all:

```
PASS — 15209 file(s) scanned, forbidden=11790 (baseline 11815)
$ git status --short
 M scripts/check/no_direct_rt_baseline.txt      # 11815 -> 11790, unreviewed
```

11790 < 11815, so the success path rewrote the tracked baseline. Both hits were
discarded with `git checkout --`, not committed.

### What is new since 2026-08-18: the hook makes it non-optional

The original record framed this as an audit-time hazard — someone runs the gate
to read a number and dirties the tree. It is now worse in two ways:

1. **It fires from the pre-push hook, not only from a deliberate run.** The
   second occurrence here came from a `git push`, so a lane that never invokes
   the gate directly still gets its working copy mutated.
2. **It fires on a push the lane did not intend to be a write at all.** The
   second occurrence came from a push whose only content was a CI workflow edit.

**Correction, same day, so the record is not stronger than its evidence.** An
earlier draft of this section claimed a *blocked or failing* push also runs the
side effect. That was inference, not measurement, and the measurement went the
other way: three pushes rejected by `push-must-check: FAIL — no pushed refs were
provided` (a separate hook defect, see below) each left
`scripts/check/no_direct_rt_baseline.txt` **clean** — the hook chain aborts
before `check-no-direct-rt.shs` runs. The two rewrites actually observed were
(a) a deliberate direct invocation of the gate and (b) a **successful** push.
The hazard is therefore real but narrower than first written: it is
*hook-triggered and success-path-only*, not "any push attempt". Whether a push
rejected LATER in the chain (after this gate has already run) also leaves the
rewrite behind is untested, and is the obvious next probe for whoever fixes
this.

### Adjacent hook defect observed while measuring this

`scripts/check/check-push-must-pass.shs:325` (`cat > "$_refs"`; empty ⇒ die)
rejected three consecutive pushes with `push-must-check: FAIL — no pushed refs
were provided`, deterministically, for a docs-only commit, from the same command
form that had succeeded ~30 minutes earlier on the same host and remote. Not
this record's bug and not investigated further here — filed only so the next lane
that hits it does not read it as its own fault.

### Why that combination is dangerous

The rewritten number is another lane's debt record. A routine `git commit -a` or
`git add -A` in the retry loop sweeps it into an unrelated landing, silently
lowering a ratchet floor nobody reviewed — and a lowered floor is
indistinguishable from real progress after the fact. Twice from one lane in one
session makes this routine, not incidental.

### Mitigation now (mechanical, no judgement call)

- Run `git status` after **any** push, including a blocked or failed one.
- Revert baselines you did not intend to change (`git checkout -- <baseline>`).
- Commit by **explicit pathspec only** — never `git commit -a` / `git add -A`.

### Fix direction

A verification run should not write tracked state at all. Recording a *lower*
count is a deliberate, reviewable act: make it an explicit
`--generate-baseline` / `--accept` flag, exactly like
`check-unbacked-extern-ratchet.shs` and `check-test-tree-divergence.shs` already
do, and have the plain run report `forbidden=11790 (baseline 11815; run with
--accept to record the improvement)`. That keeps the ratchet honest in both
directions while making every floor change attributable to someone who chose it.

Re-verification for whoever closes this: assert on the **file**, not the verdict
— run the gate on a tree where `forbidden < baseline` and require
`git diff --exit-code -- scripts/check/no_direct_rt_baseline.txt` to be clean.
The 2026-08-18 closure evidently did not, which is how it regressed unnoticed.
