# Darwin conservative UID process-record barrier — 2026-10-29

The coalition retirement primitive can prove that no live tasks remain, but its
task-exit counters already include unreaped BSD zombies. This private component
adds an independent conservative observation: no BSD process record with a selected effective
UID has a kernel process unique-id at or above an authenticated root's unique-id.

It does not publish generic reap or V4 capability. A future broker must first
establish trusted root identity, immutable descendant UID, closed admission, and
zero live coalition tasks. With those prerequisites, all remaining descendant
records are within the scanned superset. Unrelated newer processes with the same
UID deliberately cause a timeout, including live processes; the observer never
kills or reaps them.

Every BSD state is counted. XNU removes tasks from their coalitions before
`proc_exit` finishes; a process may already be on the zombie list while its
`p_stat` is not yet `SZOMB`. Ignoring that transition would falsely accept a
record that can become a zombie after observation. The previous draft's
zombie-only filter was rejected in independent review and removed.
[Apple task termination ordering](https://github.com/apple-oss-distributions/xnu/blob/main/osfmk/kern/thread.c)
[Apple BSD exit transitions](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/kern_exit.c)

## Snapshot authority

`proc_listpids` is insufficient for absence proof under arbitrary process churn.
Its kernel buffer is capped using an earlier `nprocs + 20` sample; returned bytes
can be smaller than user capacity even when that internal allocation truncates
the list. The existing coalition retirement loop remains safe because kernel
task counters independently gate its completion.
[Apple proc_listpids implementation](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/proc_info.c)

The new observer uses `sysctl(KERN_PROC_UID)`. Its kernel `proc_iterate` helper
rechecks snapshot capacity under the process-list lock and includes active and
zombie lists. Insufficient caller storage returns `ENOMEM`; the observer retries
at most three times, bounds allocation, and never treats that error as absence.
[Apple sysctl process handler](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/kern_sysctl.c)
[Apple process-list snapshot](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/kern_proc.c)

XNU increments the process unique-id on new process creation and preserves it
across exec. Thus a descendant's identifier cannot precede its root's. For each
sampled record, the observer requests zombie-aware identity information. `ESRCH`
means that record disappeared during observation; a reused PID has a newer
identifier and is conservatively counted. Other lookup errors fail closed.
[Apple fork identity initialization](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/kern_fork.c)

The inference about absence applies after the owned coalition has no live tasks:
its descendants can then only finish exit and move to reaped during the census.
Calling this observation while the workload remains live does not establish
terminal ownership or preclude a later zombie.

## Native adversarial coverage

Run `sh scripts/check/check-sosix-darwin-uid-process.shs` on macOS.

- A real child is left unreaped with `waitid(WNOWAIT)` and blocks completion.
- A genuinely live newer child also blocks until it exits and is reaped.
- A deterministic syscall adapter presents a real retained zombie identity in
  a non-`SZOMB` state, modelling the exit transition. It must still block. This
  regression would fail if the former state filter returned.
- An older unrelated zombie remains present but is excluded by the lower bound.
- A nested child calls `setsid` and exits before observation. Its PID is never
  supplied to the observer; the UID census detects its retained zombie anyway.
- Reaping the sampled child between snapshot and identity lookup safely permits
  completion when no qualifying zombie remains.
- Injected snapshot `ENOMEM` forces a retry while retaining the real blocker.
- A permission error and a deadline crossed after snapshot cannot report success.

Each live child has an independent watchdog. The probe reaps all its direct
children and asks the nested fixture parent to reap its own child. No external
process receives a signal or wait operation.

Final verification on Darwin 25.5.0: the native-backed SSpec, including live and
transitional record regressions, executed one test and passed with zero skips
or drops, using interpreter,
no-cache, no-db, sequential, and assert-ran flags. This is explicitly designated
P1 diagnostic evidence (runtime SHA-256
`59de8c475ac8e364ebbd082d080e435a7aaffb4606d8fbc276a5372dcb3f87e6`).
No P2 rebuild, deployment, or release qualification was performed.
