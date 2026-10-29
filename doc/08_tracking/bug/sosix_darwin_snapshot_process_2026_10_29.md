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

## Explicit standalone runner follow-up

`src/runtime/tools/sosix_darwin_snapshot_runner.c` now makes this component
usable as a separately compiled native command. The only accepted profile is
`trusted-snapshot-group`; `sealed-v4` rejects before file acquisition or spawn.
Capability output is SDN and explicitly reports immutable executable,
complete descendant tree, and sealed V4 as false. This command does not change
BuildRunner/TestRunner admission and is not a substitute for the V4 receipt ABI.

The manual-first acceptance is
`doc/06_spec/03_system/lib/process/darwin_snapshot_runner_spec.md`; its modern
SSpec executes the real native check through the process facade. Actual macOS
evidence is seven executed, seven passed, zero failed, zero skipped using the
explicit P1 diagnostic interpreter; pure-Simple qualification is outstanding.
TDD first failed at missing C source, then passed the initial five native scenarios.
Independent review reproduced relative TMPDIR/cwd failure and blocking FIFO
acquisition. Absolute snapshot paths and nonblocking source open fix those
cases; two more actual native acceptance scenarios now cover them.

Strict native integration still needs a proven authority boundary. A protected
broker with executable storage outside the caller's UID plus descendant
containment would need provisioning and qualification. The current user has
no noninteractive sudo authority. A VM could supply a different boundary but
would require explicit execution-platform admission and is not this native
profile. Path rehashing, chmod 0500, group signals, or process enumeration do
not establish those missing guarantees.

The runtime source-list parity checker reports existing release roster drift
across many unrelated files; the new standalone C source has an explicit
`none` row and is not an offender. The direct-environment working guard passed.
