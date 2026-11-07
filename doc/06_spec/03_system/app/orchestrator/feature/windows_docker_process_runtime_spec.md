# Windows Docker process lifecycle and recovery

Status: NOT_RUN. Authored manual mirror of
`test/03_system/app/orchestrator/feature/windows_docker_process_runtime_spec.spl`.
No admitted SPipe/docgen/sspec-maintain or Windows execution occurred.

Requirements: REQ-WDP-001, REQ-WDP-002, REQ-WDP-004, REQ-WDP-005, REQ-WDP-006.
All observations below are scripted fixtures matched by operation, executable and
exact argv. They do not establish a live Windows capability.

| Scenario | Action | Expected result |
|---|---|---|
| Probe honesty | Read a healthy scripted engine. | Launch capability remains false. |
| Engine identity | Present Linux OS or another engine ID. | Block before image access; retain no attempt. |
| Image identity | Present Linux image metadata or another repo digest. | Block preparation. |
| Executor seam | Omit a result or supply different argv. | Explicit exhausted/mismatch failure; no implicit pass. |
| Lifecycle | Prepare, create, start and wait for exit 17. | Exact native ID retained; workload exit is 17 despite CLI exit zero. |
| Short process | Start and immediately observe exit 17. | Preserve the actual terminal observation. |
| Ambiguous create | Lose the create response. | Keep uncertainty and refuse another create. |
| Mode mismatch | Observe Hyper-V or HostProcess after create. | Reject mode; retain candidate ID for reconciliation; no name cleanup. |
| Daemon replacement | Change engine identity before start. | Block without advancing created state. |
| Operation replay | Keep semantic payload but change operation ID. | Same semantic digest/name; binding refuses new operation. |
| Recovery | Reopen with original request and full exact ID. | Recheck engine, image and ownership before retaining state. |
| Stale recovery | Use old generation, name, prefix or missing ID. | Reject before Docker access. |
| Forged metadata | Change operation, boot, mode, user or network observation. | Reject without adopting a record. |
| Exact destruction | Remove owned ID and query its exact filtered absence. | Mark destroyed only on successful empty observation. |
| Unproven absence | Fail the filtered absence query. | Preserve exited state and return blocked. |
| Running cleanup | Request non-force removal of a running workload. | Refuse before removal. |
| Truncated logs | Return an output limit with CLI exit zero. | Report failure without passing off a retained prefix as complete output. |

Caller persistence and crash reconciliation are external boundaries. No native ID
means no guessed recovery. A repeated destroy or a timeout after actual removal
can remain blocked: the provider does not convert arbitrary inspection errors to
absence. These source contracts require actual Windows execution before admission.

Common launch-admission scenarios require an explicit context bound to the semantic
request digest and operation, reject absent/expired grants before create, and
preserve the separately authorized operation timeout. Independent absence scenarios
query the exact retained ID even when the cache says exited; only successful empty
native output yields a receipt. Present IDs and failed queries yield no absence.
The provider re-observes its engine around that query and records a trusted sample.

The explicit-directory scenario compares Docker's actual Config.WorkingDir with
the bound request before creation is committed. A mismatched directory preserves
uncertainty and returns blocked. Fast terminal wait still issues a native wait
query so the receipt retains actual command/output rather than a cache-only pass.


## Actual workspace mount inspection — NOT_RUN

Managed-scoped requests, explicit working-directory requests and mounted
requests append the actual Docker .Mounts count and each Type, Source,
Destination and RW field to the exact native-ID inspection. One requested bind
must inspect as exactly one bind with exact requested host/guest path bytes and
RW equal to the inverse of read_only. Wrong type/path/mode/count and extra
hidden image volumes block the observation. No case conversion or guessed path
normalization is accepted without real Windows qualification.

An empty mount projection in managed or explicit-directory requests requires
actual zero mount count and an empty range output. Legacy unscoped v1 requests
without a directory keep their historical inspection shape; those observations
do not prove absence of mounts and must not stand in for new managed projection
evidence. The mount suffix follows optional actual WorkingDir, after the scoped
labels when present.

Authored scripted lifecycle vectors include matching read-only/read-write
creates, missing mounts, volume-for-bind substitution, changed source or guest,
unexpected writability, hidden additional mounts, and actual zero versus hidden
mounts for an explicit empty workspace projection. Existing explicit-directory
fixtures now supply and require zero actual mounts. Scripted results exercise
contract matching only; no Windows process capture or Docker effect was run.

Native follow-up must use an administrator-protected real host attempt directory,
actual no-follow/path identity checks and a Windows image whose destination
permits a bind. A build/test must read that mounted source, write expected output
when writable, and prove it reaches the host artifact directory before claiming
workspace effect qualification. These authored source/manual changes remain
NOT_RUN for compilers, tests, remote builds, native paths and Docker execution.


## Fresh configured-user fact and complete finite logs — NOT_RUN

selected_user performs the retained exact-ID/scope guard, a separate actual
container inspect Config.User query and a post-query engine identity check. It
accepts only ContainerUser with zero or one ordinary CRLF/LF terminator. Padding,
extra lines, another user and changed engine reject the fact. The result carries
the actual command, untouched stdout/stderr, CLI exit, retained exact-object
state, selected user and observation clock. This is configured-user evidence,
not a SID, ACL or process-token assertion. Authored positive/negative vectors
remain unexecuted; static projection cannot replace the native query.

Logs now request the full finite Docker logs stream by exact retained native ID,
with no --tail line truncation. Existing output bounds still reject overlimit
capture; success preserves actual stdout/stderr. Complete text capture is not a
claim of a byte-complete binary log protocol. Native log transport and complete
remote-build evidence remain NOT_RUN.
