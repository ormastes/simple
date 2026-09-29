# V4 group retirement: containment admission gap

Status: BLOCKED, source/design investigation only. Baseline: `97020f7badf`
(refreshed origin/main). Follow-up to PR #1987; dependencies #1995 and #1997
remain open. No provider capability or successful-execution claim is added.

## Concrete blockers

`src/runtime/runtime_process_owned.c` only admits LeaderOnly. The shared
`owned_async_poll_locked` waitid/WNOWAIT observation immediately proceeds to
wait4. `pov4_reconcile_gone_child_locked` consumes the leader with waitpid.
Both must defer consumption for group ownership; changing only the signal
target leaves leader-first exit and ESRCH paths unsafe.

A retained zombie leader preserves identity but is itself still a group
member. Therefore kill(-pgid, 0) cannot distinguish that leader alone from
remaining descendants. Signal delivery and pipe EOF do not prove retirement.
A userspace process scan has no established atomic membership boundary under
concurrent fork, PID reuse, or membership changes. No such scan is admitted.

The ptrace exec handshake detaches at exec and does not retain fork/clone
ownership. The existing Pure Simple `core_process_observation.spl` is V1,
not an executable V4 lifecycle twin. The V4 decoder expressly rejects tree
claims on cleanup receipts. These are implementation obligations, not places
to insert synthetic evidence.

## Viable Linux design, requiring explicit admission

A per-request cgroup-v2 owner can use `cgroup.events` populated=0 as independent
live-tree retirement evidence while retaining the zombie leader. `cgroup.kill`
provides containment-wide termination; neither its return nor cgroup.procs
enumeration substitutes for populated=0. Kernel documentation describes these
[cgroup interfaces](https://cdn.kernel.org/doc/html/latest/admin-guide/cgroup-v2.html).

That design needs a pinned, exclusively owned delegated cgroup; placement
before target exec; prevention of descendant escape and external population;
bounded event parsing/polling; and ownership through cleanup failure and ACK.
The current request has no admitted containment handle or authority contract.
Unprivileged same-credential writable cgroup paths alone do not establish an
escape-proof boundary. Retaining a directory FD alone does not establish it.

Requirements must specify whether ProcessGroup excludes setsid/setpgid escape,
whether stronger cgroup containment may satisfy that policy, and how unavailable
delegation fails. This must preserve #1995's requested-policy evidence check.
A dedicated subreaper supervisor is another design option, but changes the
parent/leader/wait4 architecture; enabling a process-wide subreaper would affect
unrelated concurrent owners. See the [subreaper contract](https://man7.org/linux/man-pages/man2/PR_SET_CHILD_SUBREAPER.2const.html).

## Handoff and evidence

Implement the selected containment owner and Pure Simple V4 twin together,
then run #1987's leader-first, closed-pipe live-child, ESRCH/EINTR, unrelated
group, bounded capture, cleanup, frozen replay, and ACK fixtures. Admission
must remain unavailable until those checks establish real evidence.

Host: Darwin; Docker context orbstack responded with no running containers.
Free host disk was approximately 1.8 GiB. No bootstrap, cache deletion, native
test, Simple test, or runtime PASS was attempted or claimed. The isolated
worktree contains this report only; no commit or push was performed.
