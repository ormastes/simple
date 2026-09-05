# Pre-push guards: no verdict reached before the caller gave up (2026-08-10)

Status: FIXED (perf + one real fail-open). Severity: HIGH — produced a real
false-green push.

## CORRECTION (read this first)

The first version of this file — and the commit message of `a2fa7c59431`, which
cannot be edited — claimed that all five guards **exited silently** on SIGTERM
and that the trap fix converted that silence into an ERROR verdict. **That claim
was wrong, and it was wrong because of a measurement error.**

I read the guard's output file **while the process was still running**, saw it
empty, and recorded "0 bytes, no verdict" as proof. The file filled in later.
That is precisely the mistake this whole investigation is about — reading a slow
guard's output before it has finished — committed while proving a fix for it.

The corrected measurement waits for full process exit each time:

| case | exit | stdout bytes | verdict |
|------|------|--------------|---------|
| **pre-fix** guard + SIGTERM | 2 | 160 | `ERROR — nothing was checked (exit 2)` |
| **post-fix** guard + SIGTERM | 2 | 160 | `ERROR — nothing was checked (exit 2)` |
| **pre-fix** guard + SIGKILL | 137 | **0** | none |
| **post-fix** guard + SIGKILL | 137 | **0** | none |

So: **SIGTERM already produced an ERROR verdict before the fix**, and **SIGKILL
is untrappable and stays silent after it**. The `VERDICT_EMITTED` trap has no
demonstrated behavioural effect under either signal. No silent-exit path was
ever reproduced.

Why the pre-fix guard still ERRORed on SIGTERM: its `cleanup` deleted `TMPROOT`
and did **not** exit, so the script limped on with its scratch dir gone, the
next git redirect failed (`cannot create /tmp/tmp.X/ls.out: Directory
nonexistent`), and `die 2 "cannot measure the base commit"` fired.

## What actually caused the false green

**The guard is far slower than its callers wait, and the caller read its output
before it finished.** The agent polled the output file for "non-empty", matched
the *selftest progress* line (`selftest 16/16 fixtures correct`), read that as a
pass, and pushed while the guard was still running.

`st_mktree` (line ~418) forked one `git update-index --add --cacheinfo` process
**per fixture file**; the fixtures add ~1,100 paths, so ~1,100 git process forks
ran before the real scan even started. Measured on 2026-08-10 with load average
48-77 and 38 concurrent guard processes from parallel agent sessions, the
selftest alone was still running at 8+ minutes — past a 600s cap.

The push itself happened to be structurally sound (hand-verified: 112,726 files,
delta 0; 16 `src/` entries in the 13..25 band; 206 `src/runtime` files above the
150 canary; 0 duplicate tree entries), and the guard now confirms that number
itself — `PASS — 6 commit(s) checked ..., reference 112726 file(s)`. But at the
time the guard established nothing, because nobody waited for it.

## Fixes, and how much each is worth

1. **The cure: `st_mktree` batches its index writes** into a single
   `git update-index --add --index-info` per fixture instead of one fork per
   file. Identical index content — same modes, blobs, paths, still fail-closed
   on non-zero git status — so all 16 fixtures are still asserted. Selftest goes
   from **>600s (unfinished, killed)** to **246s** on the same loaded machine.
   This is the change that lets the guard reach a verdict inside a caller's
   budget.

2. **A real fail-open, closed:** `NOTHING TO PUSH ... exit 0` becomes `ERROR`
   exit 2 in the tree-size, conflict-tree and markers guards. This was the one
   path that genuinely returned **success with no conforming verdict**, and the
   explicit-range branch directly beside it already treated 0 commits as ERROR.
   Demonstrated: empty range now exits 2 on all three.

3. **Hardening, with no demonstrated signal-case benefit:** `VERDICT_EMITTED`
   plus an EXIT/HUP/INT/TERM/QUIT/PIPE trap in all five guards, and `cleanup`
   now **exits** rather than letting a signalled run limp on with a deleted
   temp dir. Keep it — a run that stops without a verdict is reported rather
   than assumed — but it did not fix the incident and must not be described as
   though it did.

Nothing was weakened: no threshold moved, no fixture dropped, no check skipped.

## Verified verdict matrix (`check-tree-size-push.shs`, real range)

| control | exit | verdict |
|---------|------|---------|
| SIGTERM mid-run | 2 | `ERROR — nothing was checked` |
| empty range | 2 | `ERROR — nothing was checked` |
| forced violation (`--expect-files 5`) | 1 | `FAIL — 6 commit(s) checked, 6 structurally wrong` |
| clean range | 0 | `PASS — 6 commit(s) checked, reference 112726 file(s), 0 structural faults` |

Siblings on the same range: conflict-tree `PASS — 6 commit(s)`, markers
`PASS — 13 file(s)`, revert `PASS — 13 file(s), 0 reverts`, divergence
`FAIL ... exit 1`. Empty range on conflict-tree/markers/revert: exit 2.

### A regression the negative controls caught

The first version of the trap in `check-test-tree-divergence.shs` read `$?`
inside `cleanup()`, but that guard's trap ALSO sets `cleanup_extra=...` first,
and a variable assignment resets `$?` to 0. The result was a guard that printed
`FAIL — 856 diverged ...` and **exited 0** — strictly worse than anything being
fixed. The status is now captured in the trap body (`cl_t=$?`) and passed in.
The happy path was green throughout; only a per-path control found it.

## The actual lesson

**Read the exit code AND the last line of stdout. Never poll a guard's output
file for "non-empty".** All the guards print progress lines long before the
verdict, and these guards fork thousands of git processes — under load the
tree-size selftest alone takes ~4 minutes. Run them detached (`setsid`) with no
cap and wait for the verdict line.

A guard that has not finished looks exactly like a guard that found nothing.
That, not a silent exit, is what produced the false green — and it caught the
author of this fix as well as the agent that pushed.

## Unrelated finding surfaced during this work

`check-test-tree-divergence.shs --ref 95c0703d19d` is **RED**: 856 diverged vs
854 baselined, 2 NEW divergences not in the baseline —
`unit:lib/common/mock_spec.spl` and `unit:std/mock_spec.spl`. The push that
prompted this investigation did not clear the fourth guard. Tracked separately.
