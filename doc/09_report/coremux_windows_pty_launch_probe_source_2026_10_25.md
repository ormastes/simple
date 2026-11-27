# Configured PTY startup probe — source cycle 3

Status: **AUTHORED / NOT_RUN**. This adds an explicit provider-support surface;
it does not execute or qualify a provider. The reviewed v2 launch, environment,
conversion and close owner bodies remain unchanged. No new foreign binding,
runtime ABI, child launch, compiler invocation or commit belongs to this cycle.

## Exact contract

`std.sys.pty.configured_launch_probe_v1() -> bool` is reexported by both existing
SOSIX facades as `std.sosix.pty.sosix_pty_configured_launch_probe_v1() -> bool`.
This is a startup effect, not an availability polling API.

The generic Sys provider returns false because its legacy PTY ABI cannot carry
structured executable/argv, cwd and environment changes. Basic PTY availability
does not imply configured-launch support.

The selected Windows Sys provider calls its existing native `open(1, 1)`, then
`close(handle)` and `windows_pty_cleanup_proof_v1(handle)` exactly once. It returns
true only if the real open succeeded and both close and cleanup proof succeeded.
It performs no retries, child spawn, parent environment mutation or cwd change.
No global memoization, function-existence test, resize flag or error-string
parsing substitutes for the observation.

The server must invoke the probe once per configured owner startup, store the
result in that owner's admission state, and answer discovery/capability queries
from the stored result. False blocks full admission. The probe does not promise
that a later launch, allocation, executable or permission check will succeed.
Server integration and its single-call lifecycle are owned by the server lane.

## Registry and failure ownership

The native registry has 100000 nonreused lifetime slots and a 1024 active-owner
bound. One successful startup probe consumes one closed tombstone; successful
cleanup returns active resource accounting to its prior value. No slot is reset
or reused, and no pane handle identity changes. Capacity exhaustion fails closed.

Failed open cleanup remains in the existing native quarantine. A failed close
or cleanup proof returns false; unresolved native resources remain owned by that
registry. The server's startup rejection and existing cleanup gate must retain
that authority. Boolean failure is not a clean-drain receipt. Repeated capability
requests must not consume further probe slots.

## Platform prerequisite justification

Microsoft requires Windows 10 version 1809 or Server 2019 for
[CreatePseudoConsole](https://learn.microsoft.com/en-us/windows/console/createpseudoconsole).
The additional configured-launch APIs have older OS requirements:
[GetEnvironmentStrings](https://learn.microsoft.com/en-us/windows/win32/api/processenv/nf-processenv-getenvironmentstrings)
and [FreeEnvironmentStringsW](https://learn.microsoft.com/en-us/windows/win32/api/processenv/nf-processenv-freeenvironmentstringsw)
require XP/Server 2003;
[CompareStringOrdinal](https://learn.microsoft.com/en-us/windows/win32/api/stringapiset/nf-stringapiset-comparestringordinal)
requires Vista/Server 2008; and
[GetSystemDirectoryW](https://learn.microsoft.com/en-us/windows/win32/api/sysinfoapi/nf-sysinfoapi-getsystemdirectoryw)
requires Windows 2000.

Thus a selected, correctly linked native provider on a successfully probed
ConPTY platform has the OS prerequisites for those APIs. This is a prerequisite
inference, not execution proof for argument quoting, environment merging,
GetSystemDirectoryW, process creation, Job admission or cleanup failures.

## Authored control and pending evidence

The actual-child `windows_pty_launch_probe/main.spl` fixture now performs exactly
one configured-launch probe after its parent environment baseline, retains the
result, requires success plus zero pending cleanup, and includes the probe in
the final parent-environment comparison. Its existing later child/cleanup
assertions remain strict. The 13 unit cases are unchanged; all execution remains
NOT_RUN.

Required native evidence includes positive Windows selection, generic negative
selection, server once-per-owner storage and discovery reuse, failed open/close
admission refusal, unchanged lifetime identity semantics, and zero leaked native
resources. No provider admission or full CoreMux readiness is claimed here.
