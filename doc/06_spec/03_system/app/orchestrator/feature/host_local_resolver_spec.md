# Retained host execution resolution

Status: **AWAITING_VERIFICATION — NOT_RUN**. This is an authored manual, not execution evidence.

Executable: `test/03_system/app/orchestrator/feature/host_local_resolver_spec.spl`.
Production: `src/lib/nogc_sync_mut/orchestration/host_local_command_v1.spl`.

HOST-LOCAL-07 and HOST-HELPER-03 have three authored scenarios. The fixture runs the actual signed host executor and journal with an explicitly scripted Linux Container adapter. Its typed local-root metadata is synthetic and does not establish native enrollment or platform conformance.

1. Resolve the protected execution packet, recover and inspect the exact runtime twice, and assert that the returned Container owner advances its scripted cursor on every query. The original journal sequence and charged capacity remain unchanged.
2. Fail recovery and inspection separately. Assert that each turn returns the updated Container owner, retains the exact decoded request and capacity charge, and supplies no successful observation.
3. Corrupt the retained packet. Assert refusal before any further native query or journal mutation.

The repeated-inspection case depends on the provider's strict same-identity CREATED-to-retained-RUNNING recovery repair. No create/start replay, completion inference, or capacity release is authorized by these read operations.

No SSpec, compiler or platform test ran. Local static tools are confined to the shared CPU set 0–4.
