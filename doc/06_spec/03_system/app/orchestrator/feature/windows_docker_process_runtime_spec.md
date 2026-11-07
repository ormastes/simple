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
