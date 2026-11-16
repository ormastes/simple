# Signed TaskRef retention and access

Source: `test/03_system/app/orchestrator/feature/agent_task_authority_v1_spec.spl`.
Ten authored scenarios, **NOT_RUN**. This is a manually maintained specification,
not generated execution evidence.

The scenarios construct real Ed25519 issuer/approver signatures and call the
production signature verifier. Their context and time are synthetic unit-boundary
inputs, not proof of an installed Controller root. They check separate retain/use
actions; exact raw CR bytes; changed content with a recomputed digest; changed
attempt or Host scope; changed configuration pin or Controller epoch; forged
signatures; expiry, revocation and absent clock; strict packet canonicalization;
actual command routing and pre-root action mismatch rejection.

Positive filesystem retention, same-journal replay, attempt conflict and partial
write custody are covered by the separate TaskRef store owner specification.
Those cases are also authored and NOT_RUN. Neither suite establishes Windows
protected-root acquisition/close, native cleanup, real service authentication,
Host selection, Git worktree preparation, container execution or terminal adoption.
The combined platform composition still requires those actual runtime fixtures.
