# Windows V2 process ownership

Authored scenario manual for runtime maintainers. Evidence class: Windows
host fixture linked to the production C owner. Native qualification has not
run. V3 immutable stdin, pinned launch, V4 frozen receipts and SOSIX guest
execution remain outside this foundation.

Build and execute the C fixture on Windows:

```powershell
powershell -File scripts/check/check-owned-process-windows-async.ps1
```

Use the existing admitted native Simple runner to execute
`test/03_system/runtime/process_owned_windows_async_spec.spl` after the fixture
build. Missing Windows host or fixture produces `MissingEvidence`, never a
passing scenario. The C executable returns skip status 77 on other hosts.

| Requirement | Scenario and observable result |
| --- | --- |
| REQ-WIN-OWN-001 | Capture stdout containing NUL and separate stderr; poll with zero-sized destinations; reject collection while retained bytes remain; deliver exact partial prefixes; collect once and reject stale authority. Both retained streams share the declared cap. |
| REQ-WIN-OWN-002 | Let a zero-budget child finish naturally; terminate a positive-deadline job; synchronously cancel; retain exit code 259; acquire a descendant process handle before leader exit and require that handle to be signalled before terminal collection. |
| REQ-WIN-OWN-003 | Hold eighty children alive with distinct capabilities, then use two concurrent threads to cancel, poll and collect disjoint leases. |
| REQ-WIN-OWN-004 | Reject a negative budget and a nonexistent executable without publishing a token; repeatedly reject failed admission with unchanged native handle count; reject zero authority. |

The executable's per-suite PASS line follows its native assertions. The SSpec
also requires exit zero and empty stderr. It does not infer process behavior
from source strings or fixture presence.

Documentation generation is blocked by the available self-hosted CLI refusing
to delegate `spipe-docgen` to itself. This is an authored mirror, not a claimed
successful generated-manual run. See the foundation tracking note for evidence.
