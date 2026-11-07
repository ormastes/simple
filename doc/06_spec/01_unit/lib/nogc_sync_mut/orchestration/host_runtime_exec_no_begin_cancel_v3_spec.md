# No-Host-BEGIN cancellation specification

Executable: `test/01_unit/lib/nogc_sync_mut/orchestration/host_runtime_exec_no_begin_cancel_v3_spec.spl`.
Requirements HOST-02, ORCH-02. **NOT_RUN**, authored manual.

| Scenario | Assertion |
|---|---|
| Actual producer | Receipt publication precedes one admitted→cancelled outcome; exact digest/history qualifies, parent remains charged, no provider progress |
| Pure receipt | Actual produced bytes round trip; noncanonical/oversized/bad digest data reject; changed packet digest and scope cannot match original archive |
| Receipt before outcome | Actual final appearance triggers an unavailable clock sample; child stays admitted, interlock blocks BEGIN, receipt alone does not qualify |
| Ancestor/resume/cache | Real signed sibling admission between receipt/cancel is accepted with fresh identical proof; current history qualifies, stale supplied batch rejects |
| Invalid source edges | Explicit generic protocol-fault BEGIN/unknown then cancelled records reject despite otherwise real receipt |
| Fake endpoints | Forged commit and real commit with wrong sequence cannot qualify |
| Recorded expiry | Proof expired at the recorded time rejects through the real SDK verifier |
| Clock rollback | Current Unix/same-boot monotonic time below immutable accepted receipt refuses retry without restamping or mutation |
| Fixed proof | Expired original and separately signed changed proof both refuse immutable receipt replacement |
| Permission separation | Genuine child launch proof cannot authorize parent cleanup cancellation |
| Delegation contradiction | A present malformed delegation entry refuses metadata cancellation |
| Recurrence | Evidence stays cycle-free; producer has no native process/container/teardown/release path and uses the actual shared publisher/admitted guard |

All twelve cases use actual owned WAL/private files and real signature arithmetic.
The shared fixture never constructs a positive receipt: it invokes the actual
producer. Clock-fault selection observes the actual published final file, without
a callback counter or fake native probe. Container facts remain explicitly
scripted; no exec lease or native process is created.

Generic state transitions and private-file replacement in negative cases are
explicit protocol/corruption fixtures, not alternate production cancellation
paths. Five companion journal scenarios qualify no runtime yet; combined 17
authored scenarios are NOT_RUN. Guard/startup positive integration, native close
faults, actual native execution/containment, Windows private publication and
power-loss durability are not claimed by this source checkpoint.
