# Darwin snapshot process component

The native component now launches a locally built Mach-O snapshot with exact
argv/environment, descriptor-backed cwd, separate bounded output, monotonic
timeout and cancellation, retained-leader process-group cleanup, wait4 usage,
and generation-checked acknowledgement. This is an executable foundation,
not a production V4 provider: no existing capability or runner admission gate
changes, and neither BuildRunner nor TestRunner routes through it yet.

The image snapshot requires trusted same-UID processes and trusted directory
ancestors. Its launch is pathname based; it is not a sealed image. The caller
must exclusively own the process object, never copy or overwrite an active
object, keep SIGCHLD waitable, and own wait4 for the child. Group retirement
excludes zombies and covers members remaining in that group, not children
escaping with setsid/setpgid. Strict descendant containment and a centralized
generation registry remain prerequisites for the existing V4 contract.

Run on macOS:

```sh
sh scripts/check/check-sosix-darwin-process.shs
```

The bounded native selfcheck passed on 2026-10-29. It executes six real child
cases: exact argv/env/cwd and stdout/stderr with exit 17; TERM-ignoring timeout
requiring KILL; a surviving group descendant after leader exit; 10,000 output
bytes with a 128-byte retention bound; exit 127; and explicit cancellation.
Every case requires leader reap and group retirement before ACK, rejects
premature and wrong-generation ACK, and rejects replay after release. The
test has a 15-second emergency group-cleanup handler.

TDD began with the missing-provider-header compilation failure. Native tests
then exposed a repeated successful SIGKILL race: Darwin can report EPERM for
the dying group's unsignalable members while waitid catches up. The owner
now avoids repeating successful delivery to an unobserved leader and resumes
descendant cleanup when a post-exit group sample is positive.

Independent source review found a drain-budget underflow after short reads:
an unrestricted 4096-byte read could exceed the remaining unsigned budget.
Reads now request the smaller of buffer size and remaining budget. An injected
EINTR, one-byte read, then continuously available full chunks prove the drain
returns within its 64 KiB turn. This fault fixture complements real output
capture rather than claiming a simulated host qualification.

The native command's final output was:
`Darwin owned process snapshot component: PASS (not sealed V4)`.
The check skips other hosts with exit 77. No Phase2 rebuild or deployed
Simple/SSpec provider qualification occurred. Apple platform-signed executable
copies are not qualified by this locally built fixture.
