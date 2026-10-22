
## 2026-10-12 — F03 caller identity and trust-provider integration follow-up

This scoped local follow-up supplements the retained full research in doc/01_research/app/llm_caret/dist_build_and_caret_suite_control_research_plan_2026-10-11.md. It does not supersede that research or qualify runtime behavior.

| Inspected owner | Actual source seam | Integration consequence |
|---|---|---|
| messaging/adapter/server/http_server.spl | primitive_http_principal compares a configured bearer token and derives identity/workspace/scopes/expiry from private server configuration | Preserve adapter-derived identity; client command principal fields cannot replace it. This is a configured bearer listener, not evidence of SSH caller identity or multi-principal distributed authorization. |
| messaging/adapter/server/auth.spl | authorize consumes AuthPrincipal and checks authentication, expiry, workspace and scope | The input must come from the transport owner. Importing a caller-created authenticated flag is not an authentication implementation. |
| common/privilege/authority_token.spl | root_for/mock helpers construct textual root/mock issuer signatures | These helpers do not establish cryptographic remote issuer or human approval authority and must not substitute for the signed-grant verifier. |
| nogc_sync_mut/security/auth and nogc_async_mut/security/auth | CredentialStore exposes callback-based credential use, environment/home-file resolution, rotation/context helpers | Reuse the configured owner family for credential access; a loaded handle alone does not prove host/issuer/approver scope or protected publication. Avoid a parallel secret store. |
| workbench/distributed_authority_snapshot_v2.spl | Bounded private publisher index and exact generation/policy/revocation lookup | This is a value staging/query reference, not authenticated durable trust-root publication or an activated service. |

Required next integration: declare the existing transport/identity provider facet and produce service-owned caller context; compare it to the signed operation principal/project before durable admission; publish protected key/policy generations atomically; persist authenticated approval evidence; route only the resulting admitted command to Build's own attempt/resource owner. Keep SSH account, node identity, provider credentials and signers separate. Do not read/reparse trust files per request or import sibling-private state into Build/Client.

Runtime/provider evidence remains incomplete. The c27 producer's CLI failed RSS and its test runner failed MIR; callback execution also failed. Deployed tooling is absent, and the bounded compiler/callback verification cycles are exhausted. Host aliases for actual platform/two-host acceptance are pending user input; no enrollment or signing publication is assumed.
