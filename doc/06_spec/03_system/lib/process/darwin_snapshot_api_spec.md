# Darwin cooperative snapshot runtime API

Executable specification: `test/03_system/lib/process/darwin_snapshot_api_spec.spl`.
Native gate: `sh scripts/check/check-sosix-darwin-snapshot-api.shs`.

The gate compiles the real `runtime_process_owned.c` translation unit, then links
its object into a locally compiled Mach-O selfcheck with array/string allocator
stubs. The selfcheck calls the exported C ABI; its children execute copies of
that same Mach-O. This qualifies the source API on actual macOS. It does not
qualify the deployed Simple native facade or rebuild/admit P2.

| Requirement | Executable evidence |
|---|---|
| REQ-DARWIN-SNAPSHOT-API-001 | Capability words advertise trusted path snapshots and group-only retirement; seals, escaped descendants and platform-signed executable copies remain unqualified. |
| REQ-DARWIN-SNAPSHOT-API-002 | Strict profile is rejected before inspecting executable inputs. |
| REQ-DARWIN-SNAPSHOT-API-003 | Exact arguments with spaces, explicit environment, cwd, exit 23, embedded-NUL bytes, replay before ack, premature ack and stale-handle rejection. |
| REQ-DARWIN-SNAPSHOT-API-004 | Ten thousand bytes drained with 128 retained. |
| REQ-DARWIN-SNAPSHOT-API-005 | Deadline sends TERM then KILL, reaps leader and retires the owned group. |
| REQ-DARWIN-SNAPSHOT-API-006 | Explicit cancellation retains authority until frozen completion. |
| REQ-DARWIN-SNAPSHOT-API-007 | Duplicate environment keys, incompatible SIGCHLD and FIFO executable fail before spawning. |
| REQ-DARWIN-SNAPSHOT-API-008 | A fork child cannot cancel, acknowledge, start or collect using its inherited registry; the parent retains its live owner. |

## Qualification recorded on 2026-10-29

Actual Darwin arm64 C API: 8 cases passed, including the production-owner-object
link. P1 diagnostic interpreter SSpec: 8 passed, 0 failed. The interpreter runs
the native gate subprocess; it does not manufacture or exercise a Simple opaque
owner. Production owner native and non-Apple fallback syntax checks passed.
The production object exports all six `rt_sosix_darwin_snapshot_v1_*` symbols.
Direct environment facade guard passed.

The P1 diagnostic `check` attempt for the Simple facade reported
`no admitted cached self-hosted check worker artifact is available`. Native
Simple facade execution therefore remains unqualified. No P2 rebuild was run.
Raw SSpec evidence is recorded beside this manual.

## Operational contract

Use explicit profile 1. Invocation is `[absolute executable,cwd,args...]`;
environment is complete and never inherited. Limit fields are wall, grace and
cleanup nanoseconds followed by independent stream byte caps. Start returns
`[version,errno,opaque_handle]`; only a successful start grants authority.

Fork-inherited registries reject authority before touching inherited mutexes.
The bounded 32-slot registry serializes all calls, including polls bounded to
250 ms. Collection is replayable after the frozen/reaped/group-retired receipt.
Output returns `[version,errno,byte...]`, distinguishing a valid empty capture
from stale/busy/unsupported errors. No digest ACK is claimed.
ACK consumes the handle, including when image cleanup reports an error. Poll
errors preserve ownership. SIGCHLD must remain default and waitable, with no
foreign reaper; these preconditions must hold throughout the owner lifetime.
Runtime arrays must contain their declared Simple element types. The string
ABI retains the runtime's literal-pointer compatibility; arbitrary foreign
pointers or incorrectly typed text arrays are outside this typed API contract.

Trusted same-UID processes and temporary ancestors are required. Descendants
may escape via setsid/setpgid; their retirement is not guaranteed. Strict V4
and BuildRunner strict-provider admission remain unchanged and unavailable.
