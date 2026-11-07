# Host service peer policy and gateway specification

Executable: `test/01_unit/lib/nogc_sync_mut/orchestration/host_service_gateway_v2_spec.spl`.
Requirements: HOST-02, ORCH-02. Status: **NOT_RUN**, authored manual.

| Scenario | Observable assertion |
|---|---|
| Canonical map | Decoded UID 1001, principal, project, service scope and exact action literals round trip |
| Finite permissions | UID extrema, duplicate UID/action, wildcard identity and unknown action cases reject as specified |
| Mapping bound | 64 distinct UIDs decode; 65 reject |
| Strict wire | Unknown default, duplicate field, noncanonical newline, wrong rule type and oversized UTF-8 reject |
| Actual private load | Same-FD native EUID observation, root and exact pin are returned; a wrong hash rejects |
| Native privacy/separation | Correctly hashed 0644 file and service-EUID client entry both reject |
| Bootstrap pin | Invalid trusted pin rejects without creating a Host journal |
| Explicit status | Loaded same-root policy permits actual retained status with independent capacity literals and no provider progress |
| UID/action denial | Unmapped UID, service UID and nonallowed action reject before journal progress |
| Explicit validate | Exact common request reports executionAuthorized=false, CPU 1000/memory 512; a nonallowed status read rejects |
| Root provenance | Real private snapshot from another root rejects before journal/native progress |
| Actual signed prepare | Current signed SDK authority and real preparation expiry/release precede a new admission; returned callback owner advances journal by one, a subsequent status sees zero availability, no provider command |
| Budget subject | Mapped principal/project substitutions reject the same decoded canonical record before SDK/planning publication |
| Prepare subject/scope | Canonical envelope-only negative with another mapped subject or scope rejects before SDK authorization; it is not a successful prepare proof |
| Independent nested subjects | Canonically encoded proof, original Host and controller principal tampering each yields its exact shared-chain rejection before SDK, publication or native progress |
| Immutable snapshot | Changing owned policy bytes does not hot reload the running snapshot; old pin fails a fresh load |
| Recurrence/effects | All effect routes remain nonaccepted; actual owned SDK port and returned owner are used; no new listener/native call/gateway packet predecode; canonical close turn is retained |

Pure codec assertions use real SDN. Private-loader cases use actual retained
files and native EUID observations. Callback FRAME fixtures explicitly supply a
UID for unit composition; they do not impersonate native SDK peer verification.
Their domain roots and Container providers remain scripted fixture data.

The signed prepare case uses the shared owned-journal fixture's current-clock
authority window. It releases the existing preparation through the actual timer
primitive, creates freshly signed request bytes and checks real callback
admission/owner return. It does not fabricate a Released flag or mutate a
journal's authority alias. It does not simulate native socket send failure.

All seventeen scenarios remain NOT_RUN. Required additional native evidence:
actual pinned Ready bootstrap, every open/close cleanup state including
consumed-error without cleanup, same-UID native listener refusal, wrong kernel
UID, real SDK send/timeout failure after admission, snapshot lifetime under
controlled restart and priority control progress. Existing SDK source delegation
or source-string guards are not substitutes for those runtime cases. No
multi-UID listener, async effects or complete service qualification is claimed.
