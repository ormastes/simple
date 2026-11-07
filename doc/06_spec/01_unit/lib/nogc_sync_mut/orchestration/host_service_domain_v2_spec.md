# Persistent host service domain specification

Executable: `test/01_unit/lib/nogc_sync_mut/orchestration/host_service_domain_v2_spec.spl`.
Requirements: HOST-02, ORCH-02. Audience: host owner and gateway reviewers.
Status: **NOT_RUN**; authored manual, no generated/runtime evidence claim.

| Scenario | Observable assertion |
|---|---|
| Byte bounds | Exact operation/payload sizes accepted at the shape boundary; oversized UTF-8 and embedded NUL rejected before decoding/ownership |
| Exact request shape | Status cannot carry ignored identity/correlation fields; unknown action and read payload substitution reject |
| Bounded errors | Real SDN parse observes explicit omitted detail and recovery flags; output remains bounded |
| Invalid startup | Empty/NUL root rejects before any native factory or capability acquisition |
| Actual status | Real retained fixture journal reports independent expected available CPU/memory and one retained prepared reservation without another provider command |
| Actual projection | Shared helper validates the exact canonical request, reports no execution authority, preserves owner and does not consume another provider result |
| Correlation mismatch | Wrong outer operation rejects through the actual single-decode helper without a provider command |
| Parent budget mismatch | Wrong parent ID rejects before any planning record is published |
| Incomplete effects | All four effect routes return nonzero dispatch-required; no job ID, WAL mutation or provider execution |
| Stale/closed snapshots | Stale revision and a closed exact legacy fixture writer cannot serve successful status |
| Recurrence | Handler has no finite-CLI reopen, monolithic execute/wait/cleanup, thread callback, shell or legacy close; canonical cleanup is forwarded |

Every case uses `step(...)` and real assertions. Existing explicit provider
fixtures are scripted, and their root metadata is synthetic. Their journal setup
uses the legacy fixture API. They prove neither enrollment, native effects nor
managed open/close. No native generation handle is forged for these tests.

Required additional acceptance: actual Ready/Rejected/CleanupRequired propagation,
all canonical release states including consumed-error without cleanup, owner
retention after response-publication failure, real signed prepare/budget under
installed policy, UID/principal/project/scope binding, bounded native jobs and
control progress while wait is pending. All remain NOT_RUN/unintegrated. Explicit
rejection is not counted as completing execute/wait/control functionality.
