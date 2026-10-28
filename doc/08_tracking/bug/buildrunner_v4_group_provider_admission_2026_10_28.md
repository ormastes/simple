# BuildRunner V4 group provider admission and population proof

Baseline: release/1.0.0 `9a8952b7211`. Date: 2026-10-28.

The native BuildRunner positive gate remains blocked. Darwin V4 reports
unavailable; Linux V4 accepts LeaderOnly and rejects ProcessGroup/Tree with
ENOTSUP before executable acquisition. The guard must remain in place.
No phase2 compiler was rebuilt for this investigation.

## Fixed population decoder defect

The separate Linux grouped broker accepted `populated 0junk`, `populated 00`,
and conflicting duplicate population lines as a tree-empty observation.
Its decoder now requires exactly one complete `populated 0` or `populated 1`
line. Embedded NULs, trailing spaces/tabs, incomplete lines, duplicates, invalid values and
missing population fields fail with EPROTO without modifying the output.
Unknown complete fields remain allowed for kernel interface extensibility.

The new fixtures reproduced the old decoder failure at `assert(!valid)`.
The fixed population fixture and the full V4 host selfcheck passed on native
Linux aarch64 in an isolated Docker container. The V4 fixture now verifies
that ProcessGroup/Tree rejection returns neither a PID nor a ticket, claims
no tree-empty time, and never acquires the executable pin. An initial x86
emulation run could not run the existing ptrace lifecycle checks; this is not
recorded as provider failure or positive evidence.

Reproduce on Linux with a C compiler and permitted ptrace:
`sh scripts/check/check-process-v4-group-admission.shs`.
The script bounds each executable with timeout and returns 77 on other hosts.
These C host checks are component evidence, not Pure Simple or SPipe admission.

## Why the existing broker cannot be promoted into V4

`runtime_linux_group_owner_impl.h` uses CLONE_INTO_CGROUP for atomic placement
and a pinned cgroup directory for population observations. These establish
initial placement and group observation, but not permanent containment.
The executed process retains the broker's credentials and access to the
cgroup filesystem. No credential boundary or equivalent mechanism prevents
migration. Closing inherited cgroup descriptors alone does not prevent the
process from opening a writable cgroup path. Thus population=0 can mean
escape rather than all descendants retiring.

Its original post-clone error path also ignored cgroup.kill failure, waited
only for the leader, ignored failed group removal, and closed ownership
descriptors. A failed start could therefore lose cleanup authority; an
unbounded waitpid could also hang. A Luna review independently confirmed
this cleanup gap. The population decoder change did not address it; the
following ownership follow-up removes that post-clone failure path.

The next provider needs an explicit exclusive containment authority: worker
credentials or another enforced boundary must deny cgroup migration, placing
the child before execution. It must retain a cleanup ticket through every
post-spawn failure and establish populated=0 before retiring ownership.
V4 also needs exact exec/wait4, bounded capture, frozen replay and exact ACK
integration, followed by escaping-descendant and failed-cleanup adversarial
fixtures. The existing mechanism options remain unselected; this change
neither narrows scope nor enables the broker as a V4 fallback.

## Start ownership follow-up (2026-10-28)

Baseline: release/1.0.0 `db3e7d235b7`. The fallible monotonic-clock read now
occurs before clone3. After successful clone3, the native start commits all
ownership handles and returns the lease without another admission failure.
No caller or start-receipt ABI change is needed: existing callers receive
the lease for every successful spawn. Linux's
[CLONE_PIDFD contract](https://man7.org/linux/man-pages/man2/clone.2.html)
allocates and stores the pidfd in parent memory as part of successful clone;
the old negative-pidfd branch and blocking best-effort reap are removed.

`sh scripts/check/check-linux-group-start-ownership.shs` compiles a focused
fault-injected C host fixture. Against the old owner, a failed clock reached
clone and blocking wait, failing the no-spawn assertion. Against the fix,
the clock failure returns EIO without launching or waiting. The fixture also
checks successful lease transfer, failed cancellation, collection while a
descendant remains, failed cgroup removal, retained ownership descriptors
and blocked parent release, followed by successful collection and descriptor
closure. Both red and green were observed on native Linux aarch64 in Docker.
Luna's independent source review found no P0/P1 issue.

The fake clone and filesystem boundaries qualify owner state transitions,
not live cgroup containment or Pure Simple/SPipe behavior. No Phase2 rebuild
or V4 capability change occurred. Migration prevention, V4 receipt/ACK
integration, and live escaping-descendant proof remain outstanding. Failures
before clone can still leave empty directory/output artifacts; broker exit
after a later cleanup failure still needs persistent ownership design.

## Pending cleanup retry follow-up (2026-10-28)

Baseline: release/1.0.0 `b9b6f3102e1`, including PR #5190's start ownership
prerequisite. A timeout latched `timed_out` before writing `cgroup.kill`.
If that write failed while the leader remained alive, subsequent polls skipped
the timeout branch and could return a normal running observation without ever
retrying cleanup. Explicit cancellation likewise retained its intent flag but
did not retry a failed write during subsequent polling.

The internal owner now tracks `kill_pending` separately from timeout and
cancellation intent. Every kill attempt sets it; only a successful write
clears it. Polling retries pending cleanup independently of the timeout latch.
Persistent write failures remain errors from both poll and collect, retaining
all ownership descriptors. Successful delivery is not tree-empty evidence:
collection still requires leader reap, population zero and group removal.
The public receipt layout and V4 capability/admission guards are unchanged.

The focused `check-linux-group-start-ownership.shs` fixture now covers timeout
and cancellation failure across three subsequent poll/collect attempts,
automatic recovery without resetting intent or sending another cancel,
nonterminal successful delivery, live leader and surviving descendant
collection refusal, final collection and descriptor closure. The regression
failed against the old owner at the repeated-error assertion, then passed
with the fix on native Linux aarch64 in an isolated Docker container. Evidence
is `/private/tmp/linux-group-cleanup-retry-20261028/` (`red.stderr`,
`green.stdout`, `green.status`). These were two verification cycles; no
Phase2 rebuild, live containment qualification or Pure Simple/SPipe admission
was attempted. Luna's independent exact-diff review found no P0/P1 blocker.

The clock-read-first polling order is preserved: a failed monotonic-clock
read returns EIO before retrying pending cleanup, retaining ownership and
pending intent. This can delay retry until the clock succeeds; it does not
claim successful cleanup. Permanent kill failure still requires an external
ownership/persistence design before broker exit can be safe. Credential
containment, V4 receipt/ACK integration and the actual BuildRunner Hello gate
remain open.
