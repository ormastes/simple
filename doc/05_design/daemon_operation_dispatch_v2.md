# Shared daemon operation dispatch V2

Selected scope: DAE-01 and DAE-03 from the existing distributed Caret plan.
This change admits the previously authored shared SDK adapter; it does not
introduce another scheduler, store, operation state machine or daemon framework.

The adapter uses the release branch's `distributed_operation_journal_v2` and
`distributed_operation_state_v2`. Admission stores an immutable envelope once.
Begin commits executing intent before the domain performs an effect. Repeated
begin rejects, including recovered outcome-unknown state. Every returned journal
owner must replace the caller's previous value; stale revisions fail closed.

The domain must retain result bytes before recording a terminal digest.
Publication checks the exact retained envelope, terminal state and result digest,
then publishes before acknowledging. Failure retains the journal outcome; replay
reconstructs the response instead of repeating execution. Authentication and
current domain authorization precede every call, including retained disclosure.
Journal owners must never be exposed to remote clients.

Provenance: imported only `operation_dispatch_v2.spl`, its integration spec and
authored manual from `/home/yoon/dev/simple` on 2026-11-07. The spec's missing
explicit `fail` import was repaired. Unrelated shared-tree journal codec,
BuildRunner, compiler, host and provider changes were not imported.

Eight real integration scenarios cover duplicate and changed admission, stale
owners, intent ordering, response and acknowledgement failure, digest and
identity refusal, terminal replay, close/reopen and outcome-unknown recovery.
The manual is authored and marked NOT_RUN. No admitted self-hosted runtime is
present, so execution, core/MCP checks and production qualification remain
blocked. Source review is not an executed pass.
