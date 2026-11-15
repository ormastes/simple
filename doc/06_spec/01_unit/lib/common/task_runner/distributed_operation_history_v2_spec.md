# Canonical distributed-operation history specification

Executable: `test/01_unit/lib/common/task_runner/distributed_operation_history_v2_spec.spl`.
Requirements HOST-02, ORCH-02. **NOT_RUN**, authored manual.

| Scenario | Assertion |
|---|---|
| Empty history | Actual owned empty journal has zero events/operations/endpoints |
| Multi-event/multi-revision | Real two-event segment followed by canonical begin/failure gives exact sequences, initial admissions and enclosing commit IDs for two operations |
| Same-segment origin | Admitted/executing/cancelled events in one real segment retain executing as final source state |
| Stale/closed writer | An old CURRENT snapshot and the closed exact native owner cannot yield a valid batch |
| Index ID corruption | Changing only indexed operation_id rejects even when envelope/state/outcome still match |

Tests hold an actual owned journal while publishing multi-event fixtures through
the existing canonical generic WAL API, close the exact owner, then reopen via
the real replay parser. Golden V2 event framing is test production only, not a
second production parser. No native handle or journal owner is fabricated.
These are not native execution, cross-platform or power-loss qualifications.
