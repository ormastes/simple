# Preflight association in the real controller journal

Status: **NOT_RUN**. Authored manual; no generated/runtime PASS evidence.
Spec: `test/03_system/app/orchestrator/feature/agent_preflight_journal_v1_spec.spl`.
Requirements: ORCH-02 retained association and cancellation; HOST-02 exact child input.

Setup: read the actual `caret_agent_session.sdn` and `caret_policy_catalog.sdn`
fixtures. Create a secure temporary root, acquire the existing controller journal
writer, submit the AgentSession UID and pin its real policy. Build the expected
binding from the resulting policy source/catalog/provider/OS/architecture. No
journal, host, provider or actual CLI observation is mocked. Each scenario closes
and reopens the existing journal with a new lease nonce, then closes and removes
only its own temporary root.

| Exact step | Procedure / required checks |
|---|---|
| retains and replays exact association before generic child creation | Commit association before any child row. Check completed journal outcome and independently read exact immutable object bytes. Reopen and decode retained association, accept matching plan, refuse changed request digest, then create child using actual generic metadata API. |
| refuses changed image for one parent and child uid claimed by another parent | Change image under same parent and require refusal. Submit and pin a second actual desired UID; reject its attempt to claim the first child UID. Reopen and retain original valid association. |
| persists parent cancellation before child exists and refuses later preflight | Cancel parent before child creation. Reopen; parent marker remains cancelled, no child exists, guard reports parent-cancelled and association resubmission is refused. |
| persists exact child cancellation request and parent marker after child creation | Create exact child and unrelated control row, cancel parent, reopen. Exact child has sticky cancellation_requested, revision increments once, plan and unassigned state persist; unrelated row is unaffected, parent marker persists and guard refuses. |

The test exercises real filesystem/object/WAL/lease mechanisms through production
APIs. It does not inject a crash or prove power-loss durability. Cancellation is
an authoritative request for reconciliation; it does not prove a process stopped,
release a physical reservation, authenticate expected probe evidence or authorize
execution. The generic create call remains a trusted metadata owner API; actual
preparation/execution consumers must call the preflight guard. Builds and test
runs were prohibited for this task.
