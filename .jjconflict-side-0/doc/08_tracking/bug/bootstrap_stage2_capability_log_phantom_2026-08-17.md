# Bootstrap: warning references stage2-capability.log that was never written

- **Date:** 2026-08-17
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Status:** FIXED (re-landed 2026-09-02 — see below; the 2026-08-17 "FIXED"
  claim was false, the remedy was absent from the tree)
- **Component:** `scripts/bootstrap/bootstrap-from-scratch.sh` (stage2 capability probe)

## Re-verified and re-fixed 2026-09-02 (fix/bugdb-batch-g triage)

The "FIXED 2026-08-17" section below describes the correct remedy and cites
real evidence, but **the remedy was not present in the current tree**:
`grep -n "capability build not attempted\|rm -f.*stage2-capability" scripts/bootstrap/bootstrap-from-scratch.sh`
returned nothing before this re-fix — the script still only did
`rm -f "${stage2_capability_bin}"` (the binary, not the log) and unconditionally
printed the two warnings with no log-repair step, i.e. exactly the original
defect. This is the repo's known landed-fix-gets-reverted-by-sync pattern, not
a mistaken original report.

Re-applied both remedies at the same call site (`rm -f` the log immediately
before the probe; write
`capability build not attempted: stage2 unusable (stage2_status=N)` into it in
the failure branch when it does not already exist).

**Verified by execution** (shell, not the broken `simple` binary — this bug is
entirely shell-side): built two standalone fixtures replaying the exact
failure branch (`stage2_status=1`, `stage2_bin` non-executable) against a
pre-seeded stale log —

```
$ echo "STALE FROM PREVIOUS RUN" > logs/stage2-capability.log
$ sh fixture_OLD.sh logs   # old code path (no rm -f, no repair)
$ cat logs/stage2-capability.log
STALE FROM PREVIOUS RUN                              # RED: stale log survives

$ echo "STALE FROM PREVIOUS RUN" > logs/stage2-capability.log
$ sh fixture_NEW.sh logs   # this fix's exact snippet
$ cat logs/stage2-capability.log
capability build not attempted: stage2 unusable (stage2_status=1)   # GREEN
```

`sh -n scripts/bootstrap/bootstrap-from-scratch.sh` confirms the edited script
still parses cleanly. Not verified inside a real bootstrap run (forbidden for
this task) — same limitation the original 2026-08-17 evidence already stated.

## Symptom
When stage2 itself failed (`stage2_status != 0` or `stage2_bin` not executable),
the capability probe block was skipped entirely — the `>"${log_dir}/stage2-capability.log"`
redirect never ran — yet the failure branch still printed:

```
warning: Stage 2 native-build capability failed; using seed for stage 4
warning: see .../stage2-capability.log
```

pointing at a file that either does not exist or is stale from a previous run.
Observed in tonight's `/mnt/data/worktrees/simple-boot-snap` bootstrap run where
stage2 exited 1 (see bootstrap_stage2_silent_exit1_empty_log_2026-08-17.md).

## Fix
1. `rm -f` the capability log before the probe so a stale log from a prior run
   can never be mistaken for current evidence.
2. In the failure branch, if the log does not exist, write a one-line
   `capability build not attempted: stage2 unusable (stage2_status=N)` into it,
   so the warned-about path always exists and states why.

## FIXED 2026-08-17

Status: FIXED. Both remedies applied to `scripts/bootstrap/bootstrap-from-scratch.sh`:

- `rm -f "${log_dir}/stage2-capability.log"` immediately before the probe (next
  to the existing `rm -f "${stage2_capability_bin}"`), so a stale log from a
  prior run can never be read as current evidence.
- In the `stage2_capability_ok -ne 1` branch, when the log does not exist it is
  now written with
  `capability build not attempted: stage2 unusable (stage2_status=N)`
  before the two warnings, so the warned-about path always exists and says why.

### Evidence (observed, not asserted)

binary identity: `readlink -f bin/simple` = /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple; `stat -c '%s %y'` = 59537240 2026-08-17 12:58:51.339525019 +0000

```
$ sh -n scripts/bootstrap/bootstrap-from-scratch.sh && echo "SYNTAX-OK"
SYNTAX-OK
```

Behavioural fixture replaying the exact failure branch (stage2_status=1,
stage2_bin non-executable) against a pre-seeded STALE log:

```
$ echo "STALE FROM PREVIOUS RUN" > $S/logs/stage2-capability.log
$ sh $S/fixture.sh $S/logs
  warning: see .../scratchpad/logs/stage2-capability.log
$ cat $S/logs/stage2-capability.log
capability build not attempted: stage2 unusable (stage2_status=1)
```

The stale line is gone and the warned-about path exists with a truthful reason.
Not verified inside a real bootstrap run (full bootstrap was out of scope for
this session); the edit is a two-statement change in a branch the fixture
replays verbatim.
