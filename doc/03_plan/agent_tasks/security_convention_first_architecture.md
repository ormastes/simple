<!-- codex-design -->
# Security Convention-First Architecture Agent Tasks

## Completed This Slice

- Explorer agent: plan/docs gap analysis.
- Explorer agent: compiler implementation gap analysis.
- Main agent: implement convention-first coordinate inference and `SEC101`.
- Main agent: implement generated `layer_map.sdn` and `feature_map.sdn` plus `simple security map`.
- Main agent: implement generated `gate_map.sdn` and convention-derived gate boundaries from `src/security/gate/*.spl`.
- Main agent: implement `SEC501` for `thread_local SecurityContext` use in async functions.
- Main agent: add `ui_policy.sdn`, `report.md`, `access_matrix.sdn`, `simple security ui-policy`, and `simple security audit`.
- Main agent: implement source security `configurable` / `final` metadata and structured SDN merge validation.
- Main agent: extend `ui_policy.sdn` into a display-only permission snapshot manifest with stable observation keys and server-gate-required semantics.
- Main agent: implement first-class source `ui_policy` declarations for permission snapshot rules.
- Main agent: implement minimal `security:` grammar with `layers ...` and `isolate ...` convention sugar.
- Main agent: implement explicit task-scoped `SecurityContext` propagation helpers.
- Main agent: implement async HTTP handler dispatch scoping for reconstructed remote `SecurityContext`.
- Main agent: implement generated backend-specific `sandbox_lowering.sdn`, including Simple OS native object-capability handles.
- Main agent: implement opt-in HMAC-signed remote bearer token validation for HTTP `SecurityContext` dispatch.
- Main agent: install generated sandbox lowering metadata into the hosted runtime security registry for backend/capability observability.
- Main agent: add focused compiler tests.

## Next Candidate Tasks

- Add remote `SecurityContext` key rotation, persistent session lookup, refresh, and revocation.
- Enforce lowered sandbox plans in runtime/kernel/VM backends.
- Run all HTTP/event-loop handler execution under scheduler/fiber-owned task id propagation rather than relying on worker/fd fallback paths.
## 2026-05-23 Live KMS CI Hardening Tasks

Done:

- Add local research and domain research addenda for live KMS CI hardening.
- Add feature and NFR addenda for manual-only workflow, protected environments, hygiene coverage, and operator docs.
- Add architecture and detail design addenda for the workflow checker.
- Implement `scripts/check-live-kms-security-workflow.shs`.
- Wire the checker into `scripts/check-repo-hygiene.shs`.
- Add `doc/07_guide/security/live_kms_security_gates.md`.
- Extend `test/system/code_quality/live_kms_security_workflow_spec.spl` to require the operator guide.

Verification:

- `sh scripts/check-live-kms-security-workflow.shs`
- `sh scripts/check-repo-hygiene.shs`
- `bin/simple test test/system/code_quality/live_kms_security_workflow_spec.spl --mode=interpreter`

## 2026-05-23 Live KMS OIDC Tasks

Done:

- Add `auth` workflow input with `secret` and `oidc`.
- Add job-scoped OIDC token permission for AWS/GCP/Azure lanes.
- Add GCP OIDC login and bearer export.
- Add Azure OIDC login and Key Vault bearer export.
- Add AWS OIDC bootstrap and temporary-credential SigV4 request signing.
- Extend shell workflow checker and Simple canary for OIDC invariants.
- Extend operator guide and design/research addenda.

Pending:

- Provider-side GitHub environment/OIDC trust setup remains deployment-specific.
