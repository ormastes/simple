# Exec child resource settlement guard — authored specification

Status: **NOT_RUN / AWAITING_VERIFICATION**. Authored manual, not generated execution evidence. No build/compiler/test/native-provider campaign ran. Local editing/static processes use shared CPU affinity 0–4. Dependency-only cherry-picks of reviewed8325/573a are not new guard work.

Source: `test/03_system/app/orchestrator/feature/host_runtime_exec_cleanup_guard_spec.spl` (seven cases).

| Requirement | Actual authored prevention target |
| --- | --- |
| HOST-EXEC-RESOURCE-GUARD-01 | Actual signed child packets and SDK journal states admitted/executing/outcome-unknown/completed/failed/cancelled all retain parent charge without qualified child proof. Missing/malformed provenance fails closed. Actual signed common parent destroy is permitted, its qualified parent wait/absence receipt is retained, but direct settlement/evidence acceptance/cleanup-settled/reopen cannot infer contained child teardown. No-child control still settles successfully. |
| HOST-EXEC-RESOURCE-GUARD-02 | One validated child map per projection/startup cohort; hash-only owner-validated completion batch, not decoded skip authority. Actual historical unsafe parent completion, disjoint admitted sibling cancellation and owned reopen keep blocked parent Uncertain while unrelated sibling releases. Explicit admitted-parent ordering-fault fixture closes prepared abort/expiry, cancelled-abort projection and startup no-effect bypasses without fabricated Released flags. |

Exact authored step trace (all NOT_RUN):

| Case | Exact `step()` text |
| --- | --- |
| 1 | blocks every actual child state label from direct parent resource settlement |
| 2 | fails closed on missing or malformed retained child provenance without release |
| 3 | allows actual signed parent destroy and retains absence receipt while child blocks release |
| 4 | preserves the no-child signed cleanup success control |
| 5 | keeps completed parent charged across disjoint sibling cancellation and owned reopen |
| 6 | blocks actual prepared abort and expiry release under an admitted-parent ordering fault |
| 7 | does not release cancelled abort-label parent or mark it no-effect when child lacks proof |

The setup uses actual SDK signature verification, operation WAL, generation-owned journal lock, protected private packet/result files and Common Container API. Native Container facts/commands are explicitly scripted; NO native exec child is created and no positive child no-effect/containment proof is fabricated. Parent WAIT/destroy/independent absence uses the actual existing consumer with scripted engine replies, not enum-only success. The no-child control deliberately has no admitted child row and is not represented as child discharge.

Historical-fault tests use actual SDK transitions, not direct Released ledger flags. One records completed parent with its valid parent receipt while child remains unresolved, then performs a disjoint sibling admitted→cancelled no-effect transition. The batch's child barriers survive; exact completed target facts are checked, and real owned reopen keeps its charge. Another intentionally omits parent Host BEGIN while using actual scripted common create/start/inspect and real retained creation/observation codecs; historical admitted/cancelled labels cannot release under that contradictory provenance. This is an explicit protocol-ordering fault, never production enrollment or kernel evidence.

Fixture authority timing defaults remain inherited. The cleanup fixture explicitly provisions long-lived TEST public verification key expiry BEFORE binding digest and WAL creation, then signs actual-clock cleanup. No policy/authority alias is mutated after admission. Shared signed parent/child fixture and validated packet extraction avoid a second verifier/provenance implementation.

Missing runtime evidence: all seven cases; actual kernel/native child teardown/cgroup containment; no-Host-BEGIN cancellation receipt owner; real Windows startup/native resource inspection; complete startup invocation on a platform owner; syscall close/fault injection; profiler latency/RSS. The cohort fault case exercises real batch/SDK cancellation/reopen, not a fake Windows owner. All child labels including admitted remain conservatively blocked until the separate qualified no-effect or contained teardown consumer is implemented. Diagnostic running=false and parent object absence never settle children.
