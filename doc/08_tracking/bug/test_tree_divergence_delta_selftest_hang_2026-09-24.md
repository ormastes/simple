# `check-test-tree-divergence-delta.shs` selftest hangs on fixture 3 ("orphan-free termination [fallback]")

Date: 2026-09-24

## Symptom

`sh scripts/check/check-test-tree-divergence-delta.shs <BASE> <NEW>` (and
`sh scripts/check/check-test-tree-divergence-delta.shs --selftest` alone,
which the real invocation always runs first and is fatal on failure per
`.claude/rules/vcs.md`) hangs indefinitely rather than completing in the
documented ~1s. Reproduced on **both**:

- Windows 11, Git Bash/MSYS2
- WSL Ubuntu 22.04 (git 2.34.1), invoked non-interactively via
  `wsl -d Ubuntu-22.04 -- bash -lc '...'`

`ps aux` during the hang shows the ENTIRE process chain stopped (`STAT=T`),
not just the leaf process:

```
ormastes 207 ... Ss+  bash -lc cd ~/rb1 && timeout 300 sh scripts/check/check-test-tree-divergence-delta.shs BASE NEW > /tmp/ttd.out 2>&1
ormastes 213 ... S    timeout 300 sh scripts/check/check-test-tree-divergence-delta.shs BASE NEW
ormastes 214 ... T    sh scripts/check/check-test-tree-divergence-delta.shs BASE NEW
ormastes 216 ... T    sh .../check-test-tree-divergence-delta.shs --selftest
ormastes 225 ... T    sh .../check-test-tree-divergence-delta.shs <fxref> <fxref>
```

Three processes down the recursive selftest chain (the real invocation's own
`--selftest` call, and that selftest's own fixture sub-invocation) are all
simultaneously in state `T` (stopped) — consistent with a job-control stop
signal (SIGTSTP/SIGTTIN/SIGTTOU) hitting a whole **process group**, not one
process.

`timeout 300`'s own SIGTERM (and later SIGKILL escalation via `-k`) did
**not** terminate the hung tree within the test window: a signal whose
default action is "terminate" that is generated for an already-**stopped**
process is queued, not delivered/acted on, until the process is resumed with
`SIGCONT` (or the unmaskable `SIGKILL`, which a bare `kill -TERM`/`timeout`
default does not send). `timeout`'s default escalation is `SIGTERM` then
(after `-k`) `SIGKILL` sent to its *direct child* — in one observed run even
the `-k 15` KILL grace period elapsed without the leaf process count going to
zero, suggesting the signal is not reaching (or not being processed by) every
member of the stopped group.

Minimal, environment-independent repro: the selftest's own fixture 2
("fallback" mode, `TTD_DELTA_NO_PGKILL=1`) fails on this host even in
isolation — `sh scripts/check/check-test-tree-divergence-delta.shs --selftest`
alone reports:

```
check-test-tree-divergence-delta: selftest: PASS (1) orphan-free termination [pgkill]
check-test-tree-divergence-delta: selftest: PASS (2) a killed run still emits the ERROR verdict [pgkill]
check-test-tree-divergence-delta: selftest: FAIL (3) orphan-free termination [fallback] — child <pid> survived SIGTERM
check-test-tree-divergence-delta: selftest: PASS (4) a killed run still emits the ERROR verdict [fallback]
check-test-tree-divergence-delta: ERROR: selftest FAILED (1 fixture(s))
```

No range/BASE/NEW is involved in reproducing this — it is purely a property
of the selftest's own fixture harness, so it blocked WP1's PR #1524-lane
follow-up review request to run the real delta check
(`work/push-wp1-conflict-markers-20260924`) and would block that same request
for ANY range on this class of host.

## Root cause

`run_side()` (added 2026-09-12, the orphan/no-silent-exit hardening pass)
does:

```sh
set -m 2>/dev/null || true
TEST_TREE_DIVERGENCE_OUT="$work/$name.offenders" \
    sh "$GUARD" --ref "$sref" > "$work/$name.out" 2> "$work/$name.err" &
child_pid=$!
set +m
wait "$child_pid"
```

`set -m` (job-control / monitor mode) is toggled on immediately before
backgrounding the guard invocation, specifically so the backgrounded job
becomes its own process-group leader and `kill -TERM -"$child_pid"` (a
process-group signal) can reach its descendants from `cleanup()`.

On a host with **no controlling terminal for this process tree** — which is
exactly what a non-interactive `wsl -d ... bash -lc '...'` invocation (no pty
allocated) produces, and what several other invocation paths in this
selftest's own recursive fixture harness produce (`( ... ) &`,
`$(...)` command substitution, `exec sh "$SELF_PATH" ...`) — enabling job
control and backgrounding a job is not the inert operation it is on an
interactive shell. Depending on the shell and how the process tree's session/
controlling-terminal state was inherited, the backgrounded job (or the shell
managing it) can receive `SIGTTIN` (attempted read from a controlling
terminal it does not own) or `SIGTTOU` (attempted terminal-state-changing
operation). Neither this script nor the guard it invokes reads from stdin
directly, but stdin is never redirected for these backgrounded invocations —
it is inherited from a shell that may or may not be the terminal's foreground
process group depending on the wsl.exe / non-tty bridging in use, which is
enough to trigger the stop nondeterministically on some hosts and not others.

Critically: `SIGTTIN`/`SIGTTOU` (and `SIGTSTP`) default to **stopping the
process** — and per POSIX signal semantics, once a process is stopped,
subsequently-generated `SIGTERM` (or any signal other than `SIGCONT`/
`SIGKILL`) is only queued, not acted on, until the process is resumed. So:

1. The recursive selftest fixture backgrounds the real script
   (`sh "$SELF_PATH" <fxref> <fxref>`, `TTD_DELTA_NO_PGKILL=1` for the
   "fallback" case) as `delta_pid`.
2. That instance reaches `run_side()`, does `set -m`, backgrounds the FAKE
   guard, `set +m`, `wait`.
3. Some part of this sequence triggers `SIGTTIN`/`SIGTTOU`. Because job
   control never actually created a *separate* process group in this
   environment (dash refuses job control without a controlling tty and
   silently no-ops per this file's own pre-existing comment; a tty-less bash
   can likewise fail to establish a genuinely separate foreground group), the
   stop signal is delivered to the **whole shared process group** — the
   fixture driver, the recursive `delta_pid` instance, and (transitively)
   whatever it is waiting on all stop together. This matches the `ps aux`
   evidence above precisely (three chained processes, all `T`, simultaneously).
4. The selftest's `kill -TERM "$delta_pid"` (line ~145) is delivered to a
   process that is *already stopped* and is queued rather than run. `cleanup()`
   inside the stopped `delta_pid` therefore never executes, `kill_tree`/the
   process-group kill it would have performed on the fake guard's `sleep 300`
   child never runs, and the grandchild is never asked to terminate —
   `kill -0 "$grandchild"` still succeeds after the fixture's 5s poll window,
   which is exactly the reported FAIL.

## Fix

Two complementary changes in `scripts/check/check-test-tree-divergence-delta.shs`:

1. **Prevent the stop where practical.** Redirect stdin from `/dev/null` for
   every backgrounded invocation this script performs (`run_side()`'s guard
   launch, the selftest fixture's `exec sh "$SELF_PATH" ...`), removing the
   most common trigger (a background job inheriting a controlling terminal's
   stdin and attempting to read it — `SIGTTIN`).
2. **Recover even if it still happens.** Add a `cont_tree()` helper
   (mirrors `kill_tree()` but sends `SIGCONT`) and call it — plus a
   process-group-wide `kill -CONT -PID` — *before* every place this script
   sends `SIGTERM` to a possibly-hung descendant: inside `cleanup()`, and at
   the selftest driver's own direct `kill -TERM "$delta_pid"` /
   `kill -0 "$grandchild"` site. Waking a stopped process before asking it to
   terminate is what makes the existing `SIGTERM` (already correctly aimed at
   the right process/group by the 2026-09-12 hardening pass) actually able to
   take effect, regardless of which exact terminal-control syscall produced
   the stop.

Fixed on `work/divergence-delta-selftest-hang-20260924` from `origin/main`.
Verified the selftest completes in well under 30s on both Windows Git Bash
and WSL Ubuntu 22.04, and that a real delta run
(`origin/main` vs a real topic branch) completes and produces a correct
verdict on both hosts.

## Evidence this was blocking real work

Filed after `work/push-wp1-conflict-markers-20260924`'s review asked for
`sh scripts/check/check-test-tree-divergence-delta.shs origin/main <tip>` and
the wrapper hung on both available hosts; the verdict had to be reconstructed
manually by running the underlying `check-test-tree-divergence.shs --ref` on
each side directly and diffing the offender lists byte-for-byte (which
confirmed zero new divergence, but is not a substitute for the intended
one-command escape hatch this script exists to provide).
