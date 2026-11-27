# Caret local controller client

Source: `test/03_system/app/llm_caret/feature/orchestrator_client_spec.spl`.
Status: authored companion manual; runtime execution and docgen UNRUN.
This describes focused client regressions, not full system acceptance.

1. Build submit and inspect argv for a single controller/request identity.
   Paths containing spaces remain one argument; inspect sends no source fields.
2. Reject an implicit PATH executable, unknown action, malformed UID, or
   relative submission source before invoking a child. Reconciliation is not
   required because this client has performed no controller effect.
3. Accept a matching retained-intent receipt as confirmed metadata, with
   execution authorization false.
4. Inspect active or cancelled intent without claiming observed runtime or
   termination. Cancellation leaves the independently retained scheduling
   evidence intact.
5. Reject wrong versions, types, controller identities, UIDs, kinds, and
   authorization claims while preserving the original request identity.
6. Reject duplicate SDN keys, malformed replies, invalid digests, and unknown
   statuses. Require reconciliation with the original UID.
7. Treat process failure or missing output as unconfirmed even when stdout
   otherwise resembles a valid success receipt. No retry occurs.
8. Reject inconsistent assignment/desired-state fields and inferred runtime
   success. Metadata cannot manufacture process or termination evidence.
9. Accept complete unassigned/bound metadata field sets; reject missing host
   evidence or invalid generations. Retained assignment is still not execution.
10. Reject saturated byte capture and unsolicited stderr before confirming a
    receipt, preserving reconciliation with the original UID.

Requirements: REQ-CARET-CONTROLLER-001 through REQ-CARET-CONTROLLER-003 in
`doc/05_design/caret_orchestrator_client.md`.
