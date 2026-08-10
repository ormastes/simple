# All four pre-push guards could exit SILENTLY with no verdict line (2026-08-10)

Status: FIXED (this commit). Severity: HIGH — produced a real false-green push.

## Symptom

`scripts/check/check-tree-size-push.shs` produced **no verdict line at all** on
a real commit range. An agent polling the guard's output file for "non-empty"
matched the guard's *selftest progress* line
(`selftest 16/16 fixtures correct`), read that as a pass, and pushed. Re-running
the guard retroactively on the landed range `a981699b686..95c0703d19d` still
emitted no verdict.

That particular push happened to be structurally sound (hand-verified: 112,726
files, delta 0; 16 `src/` entries in the 13..25 band; 206 `src/runtime` files
above the 150 canary; 0 duplicate tree entries) — but the guard did not
establish that. It established nothing.

## Root cause

`scripts/check/check-tree-size-push.shs:157-158` (pre-fix):

    cleanup() { [ -n "$TMPROOT" ] && rm -rf "$TMPROOT"; }
    trap cleanup EXIT INT TERM

The trap removed the temp dir and **printed nothing**. So every way the process
could stop that was not an explicit `die` / PASS / FAIL — a SIGTERM from a
caller's 600s Bash cap, an earlyoom kill, a Ctrl-C, a `set -u` abort — ended the
run with an **empty stdout and no verdict**.

Two things made that reachable rather than theoretical:

1. **The guard is slow enough to hit a caller's timeout.** `st_mktree`
   (line ~418) forked one `git update-index --add --cacheinfo` process **per
   fixture file**; the fixtures add ~1,100 paths, so ~1,100 git process forks
   ran before the real scan even started. On a loaded machine (load average 48
   measured on 2026-08-10, with 10+ concurrent guard runs from parallel agent
   sessions) that alone outlasted the 600s cap.
2. **Silence is indistinguishable from "not finished yet."** A caller polling
   the output file cannot tell "killed, checked nothing" from "still running",
   which is exactly the confusion that produced the false green.

## Reproduction (measured)

| run | exit | stdout |
|-----|------|--------|
| pre-fix guard, SIGTERM at 20s | 143 | **empty — 0 bytes, no verdict** |
| pre-fix guard under 600s cap | 124 | no verdict reached |
| pre-fix `--selftest`, loaded machine | — | still running at 8+ min |

## The same defect in ALL FIVE guards

This was never a one-guard bug. Every mandatory pre-push guard — including
`check-no-revert-push.shs`, which landed at origin *while this fix was being
written* — had a trap that cleaned up and printed nothing, or no trap at all:

| guard | pre-fix trap |
|-------|--------------|
| `check-tree-size-push.shs` | `trap cleanup EXIT INT TERM` — cleanup printed nothing |
| `check-no-conflict-markers-push.shs` | `trap cleanup EXIT HUP INT TERM` — cleanup printed nothing |
| `check-no-conflict-tree-push.shs` | **no trap at all** |
| `check-test-tree-divergence.shs` | `trap 'rm -rf ...' EXIT INT TERM` — printed nothing |
| `check-no-revert-push.shs` | `trap cleanup EXIT INT TERM` — cleanup printed nothing |

So *any* "guards PASS" claim made by polling a guard's output file, rather than
by reading its exit code AND a verdict line, is unsound for all five. That the
newest guard was written with the same defect, by a different session, on the
same day, is the point: the verdict convention was documented but the
**silence** case was never part of it, so each new guard reproduced the hole.
The convention now covers it explicitly (`.claude/rules/vcs.md`), and any sixth
guard must carry the `VERDICT_EMITTED` trap.

## Fix

1. **The no-silent-exit invariant, in all four guards.** A `VERDICT_EMITTED`
   flag is set by every legitimate verdict (`die`, every PASS, every FAIL). The
   EXIT/HUP/INT/TERM/QUIT/PIPE trap synthesises
   `ERROR — nothing was checked (exit 2)` whenever the process stops without
   one, and names the signal (143 harness cap / earlyoom, 130 Ctrl-C, 129
   SIGHUP, 131 SIGQUIT, 141 SIGPIPE) because those root-cause differently.
2. **The `NOTHING TO PUSH ... exit 0` path is now `ERROR` exit 2** in the
   tree-size, conflict-tree and markers guards. It was the one path that
   returned success with no conforming verdict — and the explicit-range branch
   directly above it already treated 0 commits as ERROR, so this is the
   consistent reading of the convention, not a new rule. A run that checked
   nothing cannot report a pass.
3. **`st_mktree` batches the index writes** into a single
   `git update-index --add --index-info` per fixture instead of one fork per
   file. Identical index content — same modes, blobs, paths, still fail-closed
   on non-zero git status — so the selftest still asserts all 16 fixtures. The
   selftest went from >600s (unfinished) to **246s** on the same loaded machine.
   This is what lets the guard reach its verdict inside a caller's timeout; it
   does not reduce what is checked.

Nothing was weakened: no threshold moved, no fixture dropped, no check skipped.

### A regression the negative controls caught

The first version of the trap in `check-test-tree-divergence.shs` read `$?`
inside `cleanup()`, but that guard's trap ALSO sets `cleanup_extra=...` first,
and a variable assignment resets `$?` to 0. The result was a guard that printed
`FAIL — 856 diverged ...` and **exited 0** — strictly worse than the bug being
fixed. The trap now captures the status in the trap body (`cl_t=$?`) and passes
it in. This is exactly why each verdict path needs its own negative control:
the happy path was green throughout.

### What a trap can and cannot do

A SIGTERM arriving while the shell waits on a foreground child is handled only
after that child returns, so a killed guard prints its ERROR verdict *late*
rather than instantly (measured: ~2 min later, mid-selftest). And **no trap can
catch SIGKILL**. The trap therefore guarantees a verdict for every stop the
shell can observe; staying inside the caller's budget is what the performance
fix buys, and running the guards detached with no cap is the caller's half of
the contract.

## How to call these guards correctly

Read the **exit code** and the **last line of stdout**. Do not poll the output
file for "non-empty" — the guards print progress lines (selftest results,
per-commit findings) long before the verdict, and matching one of those is what
caused this incident.

## Unrelated finding surfaced during this work

`check-test-tree-divergence.shs --ref 95c0703d19d` is **RED**: 856 diverged vs
854 baselined, 2 NEW divergences not in the baseline —
`unit:lib/common/mock_spec.spl` and `unit:std/mock_spec.spl`. The push that
prompted this investigation did not clear the fourth guard. Tracked separately.
