# Protected broker control boundary specifications

Status: AUTHORED_NOT_RUN. Eight executable DATA cases are in `test/01_unit/lib/nogc_sync_mut/io/linux_protected_broker_control_v1_spec.spl`. They do not prove filesystem mutation, descriptor custody, compiler privacy, broker termination, or end-to-end recovery.

| Requirement | Actual executable assertion |
|---|---|
| REQ-BROKER-01 | Original positive monotonic budget admits exact upper boundary and rejects expired/negative/oversized bounds. |
| REQ-BROKER-02 | Waiting replay requires identical identity and original deadline. |
| REQ-BROKER-03 | Reserved, prepared, publishing and uncertain phases cannot restart publication. |
| REQ-BROKER-04 | ACK-consumed, durable-proof-required and reap-consumed remain distinct refusals. |
| REQ-BROKER-05 | Expiry remains terminal and a later deadline does not rearm. |
| REQ-BROKER-06 | Unknown phases are rejected. |
| REQ-BROKER-07 | Only exact mutable request/response names are reserved from retained caching. |
| REQ-BROKER-08 | Unknown-origin defaults explicitly have facts_known=false and no evidence. |

## Actual Host/native fixture composition

The separate Host owner implements `test/fixtures/orchestration/host_live_broker_cycle7_fixture_v7.spl`. Its functions must take a genuine installed Host owner from persistent service setup, invoke the actual public Host cancel/step/reap paths, and return every updated owner/rejected reader/continuation before inspecting errors. The lower IO fixture may not create a friend-package public wrapper accepting a reader plus DTO; that would itself introduce the forbidden mutation bypass.

Required combined cases are: a copied Host owner performs two begin calls and obtains one canonical nonce/request; an independently opened read-only root cannot mint a journal claim; a missing/unsafe child produces retained opening custody and no repeated acquisition; old nonce or changing response stays pending; a matching cancellation ACK is consumed once without Host completion; original deadline is unchanged; existing exact reap is idempotent and a mismatch cannot replace it; copied original readers cannot close an adopted child; authorized per-operation release drains exact child resources while stale aliases remain tombstoned; parent cleanup preserves its writer until child drain completes. Partial writes/rename-sync uncertainty must retain stage identity and never become release evidence.

Those native scenarios are NOT_RUN. The persistent service driver and controllable live fault scheduling are external integration prerequisites, not supplied or simulated by the eight DATA cases. Compiler outsider/member/constructor/alias negatives belong to the real strict+Deny compiler lane and remain separately qualified. No runtime, native, branch coverage or complete recovery PASS is claimed here.
