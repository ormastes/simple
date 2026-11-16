# Signed workspace invocation V1

Status: **AUTHORED / NOT_RUN**. Handwritten companion to
`test/03_system/app/orchestrator/feature/agent_workspace_invocation_v1_spec.spl`.
No generated SPipe or passing runtime receipt exists.

Requirements: REQ-WORKSPACE-AUTH, REQ-WORKSPACE-BIND,
REQ-WORKSPACE-RETENTION from the accepted single-primary workspace design and
Host effect/lifetime addenda.

| Authored scenario | Expected assertion |
| --- | --- |
| Exact full-manifest round trip | Raw CRLF task bytes, ordered inner argv, canonical stage manifest and fixed deadline survive unchanged. Full signed packet round-trips. |
| Strict authority/schema | Wrong/missing/unknown/duplicate/noncanonical fields and bootstrap-only intent, action list, clock or exec-authority profile fail. |
| Exact task/use/source binding | Namespace, task digest, desired source/catalog and outer session/attempt substitution fail before effects. |
| Complete invocation approval | Changed model, argv, selection binding, stage slot or deadline invalidates the earlier real Ed25519 approval. |
| Independent explicit action | Host-execute-only roles or the ordinary Host grant/approval cannot authorize `agent_session_invoke_v1`; either corrupt signature fails. |
| Fresh context binding | Changed Host operation, installed-policy digest, actual scope, expiry or revocation invalidates the signature check. |
| Bounded continuation DATA | Oversized/NUL argv, duplicate credentials and preparation duration beyond the signed workload bound fail. |
| Actual journal retention | A real owned Host journal archives complete inputs with exact readback; exact retry succeeds and changed manifest under the same identity fails. Typed owner close checks cleanup, state and diagnostics. |

The signature scenarios use explicit deterministic **test** keys and the actual
snapshot verifier. Their constructed public policy is test DATA, not evidence of
installed Host authority. The archive scenario opens the actual filesystem and
owned journal; its opaque request DATA is shape-only and is never executed.
No fake probe selection or source owner is used for a positive effect assertion.

The production source calls actual source-owner projection/program correspondence
and anchored stage methods after real Host capacity begin. A missing positive
combined owner fixture means these composition paths remain unexecuted and do
not have claimed coverage. Required later actual-owner negatives include stale
source generation, changed installed profile/slot, begin error after WAL,
partial staging owner retention, copied continuation, expired/revoked authority
before each continuation, mismatched native request bootstrap digest, and
workspace provider first-start configuration rejection.

An actual live launch additionally requires the original machine workspace
admission, Git/worktree/bootstrap/exec/observation and persistent terminal owner
dependencies. The internal staging slice has no end-user route, reports no
AgentObserved/InteractiveReady, and returns every charged/partial owner even
when launch remains unavailable.
