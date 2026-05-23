<!-- codex-design -->
# Security Convention-First Architecture Detail Design

## Data Flow

1. `infer_security_coordinate(path)` extracts `layer`, `feature`, `trust`, `runtime`, and `security_root`.
2. `build_feature_graph` extracts source-level imports and call-like references.
3. `build_hir_feature_graph` extracts resolved HIR imports and referenced symbols when modules are available.
4. `source_security_violations_sdn_with_modules` emits diagnostics.

## Coordinate Inference

For `src/<layer>/<feature...>/<file>.spl`, the first segment after `src` is accepted when it is one of the built-in layers. The feature is the remaining directory path, excluding the file name, joined with dots.

Example:

`src/service/user/profile/profile_service.spl` -> `layer=service`, `feature=user.profile`.

## SEC101

`SEC101` is emitted only for same-feature edges with both source and target layers known.

The initial rule is conservative:

- `to_layer_index > from_layer_index + 1` is a skip.
- Same layer and adjacent layer are not reported by this diagnostic.

## Tests

Compiler tests cover:

- Convention-first coordinate inference.
- `ui -> domain` same-feature import reports `SEC101`.
- `service -> domain` same-feature import does not report `SEC101` or `SEC201`.
## 2026-05-23 Live KMS CI Hardening Detail Design Addendum

Files:

- `scripts/check-live-kms-security-workflow.shs`: validates workflow invariants and runs `actionlint` if available.
- `scripts/check-repo-hygiene.shs`: invokes the live KMS checker as part of the existing hygiene gate.
- `doc/07_guide/security/live_kms_security_gates.md`: operator guide for environments, secrets, manual execution, and OIDC direction.
- `test/code_quality/live_kms_security_workflow_spec.spl`: guards the workflow and guide from the Simple test side.

Checker behavior:

- Fail if the workflow file is missing.
- Fail if `push`, `pull_request`, or `schedule` triggers appear at top-level workflow trigger indentation.
- Require `workflow_dispatch`, `choice` provider input, `permissions: contents: read`, concurrency, four provider jobs, four protected environments, credential preflight, and the live KMS integration spec command.
- Run `actionlint` only when present on `PATH`.

Error handling:

- Structural violations print `VIOLATION: live KMS workflow: ...` and exit non-zero.
- Repo hygiene converts that failure into a normal hygiene violation.

## 2026-05-23 Live KMS OIDC Detail Design Addendum

Workflow changes:

- Add `auth` input with `secret` and `oidc`.
- Keep top-level `permissions: contents: read`.
- Add job-scoped `permissions: contents: read, id-token: write` for AWS/GCP/Azure jobs.
- Add OIDC setup preflight steps before provider auth actions.
- For GCP, use `google-github-actions/auth@v2` with `token_format: access_token`, then write `SIMPLE_LIVE_KMS_GCP_BEARER` to `GITHUB_ENV`.
- For Azure, use `azure/login@v2`, then write `SIMPLE_LIVE_KMS_AZURE_BEARER` from a Key Vault access-token query to `GITHUB_ENV`.
- For AWS, use `aws-actions/configure-aws-credentials@v4`, probe `aws sts get-caller-identity`, export `SIMPLE_LIVE_KMS_AWS_AMZ_DATETIME`, and let the Simple live spec sign the AWS KMS request from temporary AWS credentials.

Checker changes:

- Require `auth`, `id-token: write`, OIDC setup variables, official provider auth actions, and bearer export steps.

Adapter changes:

- Add AWS SigV4 temporary-credential request builders that include `x-amz-security-token` in both emitted headers and the signed header list.
