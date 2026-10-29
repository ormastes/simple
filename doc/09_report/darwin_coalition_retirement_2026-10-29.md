# Darwin kernel coalition retirement primitives — 2026-10-29

The earlier process-group negative evidence remains valid. A different native
kernel mechanism now has positive bounded evidence: a user LaunchAgent receives
its own resource coalition, descendants retain membership across `setsid`,
`setpgid`, and double fork, and the supervisor can safely signal process
incarnations with `proc_signal_with_audittoken`.

The private runtime component implements bracketed membership/identity reads,
PID-version-checked signals, bounded census allocation, deadline-bounded repeated
retirement, and kernel task-counter completion. It rejects its caller's coalition
and unknown coalition IDs. It never treats an empty process census as completion.

**This is not a complete strict process provider.** A trusted broker must first
establish exclusive coalition authority and close launch admission. This helper
does not supply that authority. No generic V4 capability is enabled. In
particular, the receipt's `all_reaped` field remains false.

## Executable evidence

`sh scripts/check/check-sosix-darwin-coalition.shs` uses real temporary user
LaunchAgents under `gui/<uid>` and cleans up their registrations. Fixtures have
independent 20-second watchdogs. No privilege escalation or persistent service
installation is performed. Requires a C compiler and Python's plist encoder.

- After either leader kill or normal exit, all three escape forms remain alive
  after launchd group cleanup and retain the original coalition ID.
- Retirement uses the kernel PID version, not an unguarded PID signal. A stale
  token returns `ESRCH` without killing the intended current process.
- A deterministic test hook requests a fresh fork **after** the first complete
  census. That child is absent from the initial list. The kernel's nonzero task
  count requires a later pass; all live tasks are retired.
- Kernel `NOTE_REAP` events and zombie-aware identity reads separately prove
  reaping for the three named adversarial fixtures. That finite observation is
  not extrapolated to all unobserved production descendants.
- A deliberately unreaped zombie already increments `tasks_exited`. Therefore
  equal task counters cannot stand in for a generic reap receipt.
- The current coalition and an unknown coalition are rejected without signals.

The first integration run exposed `LaunchOnlyOnce` auto-removal on normal exit:
`bootout` returns 3 after launchd has already removed that job. The fixture now
allows that result only in the normal-exit scenario. Native verification then
passed on Darwin 25.5.0, uid 501, including the deterministic post-census fork.

The SSpec then exposed a fixture diagnostic token exceeding its bounded parser
width; the token was shortened and worker stderr is now forwarded on failure.
The complete native-backed SSpec subsequently passed: one executed, one passed,
zero failures/skips/drops with interpreter, no-cache, no-db, sequential, and
assert-ran flags. This is P1 diagnostic evidence using SHA-256
`59de8c475ac8e364ebbd082d080e435a7aaffb4606d8fbc276a5372dcb3f87e6`,
not P2 release qualification. The earlier designated P1 generation had been
removed; no runtime rebuild was attempted.

## Kernel authority and remaining boundary

Apple's kernel explicitly rejects nonprivileged attempts to select a different
spawn coalition, except for tasks with the private coalition-spawn entitlement.
Fork/spawn inherits the existing resource coalition. A launchd-created unique
coalition therefore has stronger membership than a mutable process group.
[XNU spawn coalition checks](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/kern_exec.c)

The kernel signal API resolves an audit token rather than relying only on a
numeric PID. The native test confirms PID-version rejection. The dynamic symbol
is checked before use; absent support returns `ENOTSUP`.
[XNU audit-token signalling dispatch](https://github.com/apple-oss-distributions/xnu/blob/main/bsd/kern/proc_info.c)

Task counters are copied from the resource coalition under its lock. Coalition
IDs increase monotonically. Kernel coalition deallocation requires zero active
tasks, termination, and coalition reap, so disappearance of a previously
validated coalition is sufficient to report task emptiness. It is not proof that
all BSD zombie process records have been reaped.
[XNU coalition lifecycle](https://github.com/apple-oss-distributions/xnu/blob/main/osfmk/kern/coalition.c)

Production integration still needs:

1. Authenticated launchd registration and worker handoff; the test's temporary
   plist/output file is fixture plumbing and not a same-UID-resistant protocol.
2. Demonstrated closure of job restart/admission, including malicious replacement
   of same-UID registrations and authenticated `SpawnConstraint` handling.
3. A worker policy preventing privileged credential changes or delegation to
   unrelated launchd services. Image CDHash/library constraints alone do not
   supply those restrictions.
4. Proof of reap for descendants that fork and exit between observations. The
   coalition count does not provide it; PID1 performs orphan reaping.

Until these are implemented and verified, this component is a useful kernel
retirement building block and must remain separate from full V4 qualification.
