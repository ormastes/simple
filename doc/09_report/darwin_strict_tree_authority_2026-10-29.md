# Darwin strict descendant authority — 2026-10-29

The current unprivileged native Mac process owner cannot satisfy arbitrary
all-descendant termination and reaping. This change supplies executable negative
qualification, not a replacement owner or a completed strict V4 implementation.
No capability bit, process API, P2 runtime, or deployment artifact is changed.

## Native evidence

Host: Darwin 25.5.0, uid 501. Run:

```
sh scripts/check/check-sosix-darwin-strict-tree.shs
```

The native C probe passed on this host:

| Probe | Observed result |
|---|---|
| Child `setsid`, leader exit and group kill | Child survives both |
| Child `setpgid`, leader exit and group kill | Child survives both |
| Double fork after `setsid`, leader exit and group kill | Grandchild survives both |
| `waitpid` of escaped descendant by observer | `ECHILD` in all six cases |
| kqueue `NOTE_FORK | NOTE_TRACK` | `ENOTSUP` |
| Seatbelt `deny process-fork` | `fork` and `posix_spawn` return `EPERM` |
| `setsid` under that Seatbelt policy | Succeeds |

Each escape test keeps the leader unreaped until after group signalling, so the
negative result is not caused by PID reuse. The survivor must reply through its
inherited pipe after group cleanup. A second pipe command makes it exit; a
previously registered kqueue `NOTE_EXIT` confirms termination. A child watchdog
also bounds fixture lifetime if an assertion fails. No escaped numeric PID is
used for signalling. Reaping the leader is verified separately.

`--require-strict` runs the same evidence then returns 78. Its failure is
intentional: the requested strict acceptance criterion remains unmet. The
SSpec checks this failure and all six escape markers. A green SSpec here means
the refusal is correct; it does not mean containment is implemented.

## Candidate authority assessment

1. **Process groups / launchd jobs:** Apple documents that launchd cleanup is
   limited to processes with the job's process group ID. This does not cover a
   successful `setsid` or `setpgid` escape.
   [Apple launchd.plist source](https://github.com/apple-oss-distributions/launchd/blob/main/man/launchd.plist.5)
2. **Seatbelt membership constraints:** XNU's `setsid_internal` and `setpgid`
   implementations perform session/group checks but have no MAC authorization
   hook. A proposed profile operation alone cannot add a kernel hook. Denying
   process creation gives a narrower no-child execution model and rejects
   legitimate descendant creation; it does not implement the requested model.
   [Apple XNU kern_prot.c](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/kern_prot.c)
3. **Recursive kqueue:** XNU explicitly rejects `NOTE_TRACK`, `NOTE_TRACKERR`,
   and `NOTE_CHILD`. Individual exit notifications provide observation, not a
   non-escapable container or inherited wait authority.
   [Apple XNU kern_event.c](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/kern_event.c)
4. **Coalitions:** XNU gates coalition creation/termination on membership in a
   privileged coalition. Coalition termination prevents new spawn admission
   but permits existing members to fork. It is not an unprivileged atomic
   terminate-all/reap primitive. No privileged call or entitlement is assumed.
   [Apple XNU sys_coalition.c](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/sys_coalition.c)
5. **Endpoint Security:** Apple exposes fork as a notification event. The
   documented authorization event set contains no fork authorization. An event
   observer plus later PID signalling is not proof of complete, race-free
   descendant retirement. An ES collector also does not transfer parenthood.
   [Apple ES fork event](https://developer.apple.com/documentation/endpointsecurity/es_event_type_notify_fork)
   [Apple ES event types](https://developer.apple.com/documentation/endpointsecurity/es_event_type_t)

These are scoped conclusions from the inspected Apple APIs and live probes,
not a proof about every private Apple facility. A production strict provider
still needs a demonstrated kernel authority: non-escapable membership,
admission closure before retirement, identity-safe termination, and trustworthy
exit/reap completion. A privileged broker or VM changes the deployment and
authority model and needs separate design and live verification. Merely adding
a privileged broker around the same process-group code does not solve it.

## SSpec diagnostic evidence

`sosix_darwin_strict_tree_authority_spec.spl`: 1 executed, 1 passed, 0 failed,
0 skipped, 0 dropped, with `--mode=interpreter --no-cache --no-db --sequential
--assert-ran`. This used the explicitly designated P1 bootstrap diagnostic
runtime, SHA-256 prefix `ddd5aa`, and the worktree's own `SIMPLE_LIB=src`.
It is diagnostic evidence, not pure-Simple P2 release qualification. An initial
run referencing the unrelated main worktree's library returned failure; after
materializing the sparse worktree's library and using it, the diagnostic passed.
No runtime rebuild or deployment was performed.

## Landing validation

The native strict checker was rerun on macOS against the current release base:
all six escape markers, the kqueue refusal, and Seatbelt denial reproduced;
`--require-strict` returned the intentional status 78. The SSpec now registers
an explicit non-macOS skip, preserving every Darwin assertion. This platform
guard is source-reviewed; the updated SSpec has not been executed through a
qualified pure-Simple runner. No strict containment or release qualification is
claimed.
