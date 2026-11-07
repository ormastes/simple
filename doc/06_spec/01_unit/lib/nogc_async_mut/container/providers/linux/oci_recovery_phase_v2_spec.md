# Recovery phase replay

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_recovery_phase_v2_spec.spl`.

Manual source mirror: six authored scenarios, UNEXECUTED. No native runtime qualification.

| Scenario | Assertion |
|---|---|
| Repeated receipt | Actual common create → recover running → fresh inspect → recover exited; original created and current exited receipt replays preserve exact identity and consume fresh queries. |
| Immutable rejection | Changed seven identity fields, unsafe native ID, ineligible phase and changed bound payload reject before another executor attempt. |
| Tombstone | Created receipt cannot adopt destroyed retention; exact destroyed receipt reconciles without native query and cannot produce absence without its independent query. |
| Legacy compatibility | Exact legacy phase reconciliation remains available; legacy created-to-running relaxation is refused. |
| Prepared compatibility | Exact V2 PREPARED empty-ID reconciliation retains existing scoped name discovery and verifies returned full native identity. |
| Stopped replay | Original created and current stopped receipts recover exact retained stopped identity. |

The adapter keeps every existing exact identity/phase path. The only new relaxation is expected CREATED against retained RUNNING, EXITED or STOPPED, requiring matching canonical full64 native IDs and a separately validated V2 request binding. Unknown, corrupt, changed-payload or legacy bindings cannot authorize that relaxation. Lifecycle transitions remain the provider's responsibility. Build/check/test execution was not performed.
