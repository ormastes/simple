# Live KMS Security Gates

The live KMS workflow is an opt-in credentialed gate for the security runtime adapters. Normal CI should stay hermetic; this workflow exists to prove that the adapter request builders still work against real AWS KMS, Google Cloud KMS, Azure Key Vault, and PKCS#11 HSM gateway deployments.

Workflow:

- `.github/workflows/live-kms-security.yml`
- Trigger: `workflow_dispatch` only
- Provider input: `aws`, `gcp`, `azure`, `hsm`, or `all`
- Protected environments: `live-kms-aws`, `live-kms-gcp`, `live-kms-azure`, `live-kms-hsm`
- Test: `test/integration/lib/security/live_kms_transport_spec.spl`

Repository hygiene also runs `scripts/check-live-kms-security-workflow.shs` to keep this workflow manual-only, environment-scoped, and fail-fast on missing credentials. If `actionlint` is installed locally, that script runs it before the invariant checks.

## Environment Setup

Create one GitHub environment per provider and configure required reviewers. Environment secrets should be preferred over repository secrets so a selected provider job can only read its credentials after the environment rules pass.

AWS environment `live-kms-aws`:

- `SIMPLE_LIVE_KMS_AWS_ENDPOINT`
- `SIMPLE_LIVE_KMS_AWS_KEY_ID`
- `SIMPLE_LIVE_KMS_AWS_AUTHORIZATION`
- Optional: `SIMPLE_LIVE_KMS_AWS_ALGORITHM`
- Optional: `SIMPLE_LIVE_KMS_PAYLOAD`

GCP environment `live-kms-gcp`:

- `SIMPLE_LIVE_KMS_GCP_ENDPOINT`
- `SIMPLE_LIVE_KMS_GCP_KEY_VERSION`
- `SIMPLE_LIVE_KMS_GCP_BEARER`
- `SIMPLE_LIVE_KMS_DIGEST_SHA256`

Azure environment `live-kms-azure`:

- `SIMPLE_LIVE_KMS_AZURE_VAULT`
- `SIMPLE_LIVE_KMS_AZURE_KEY`
- `SIMPLE_LIVE_KMS_AZURE_BEARER`
- `SIMPLE_LIVE_KMS_DIGEST_BASE64URL`
- Optional: `SIMPLE_LIVE_KMS_AZURE_ALGORITHM`

HSM environment `live-kms-hsm`:

- `SIMPLE_LIVE_KMS_HSM_ENDPOINT`
- `SIMPLE_LIVE_KMS_HSM_SLOT`
- `SIMPLE_LIVE_KMS_HSM_KEY`
- `SIMPLE_LIVE_KMS_HSM_AUTHORIZATION`
- Optional: `SIMPLE_LIVE_KMS_HSM_MECHANISM`
- Optional: `SIMPLE_LIVE_KMS_PAYLOAD`

## Operating Rules

- Keep the workflow manual-only; do not add `push`, `pull_request`, or `schedule` triggers.
- Keep `permissions: contents: read` unless a provider lane is changed to use GitHub OIDC.
- Prefer short-lived cloud credentials. For AWS/GCP/Azure, the better long-term path is OIDC federation from GitHub Actions to the cloud provider, with the environment gate controlling who can request the OIDC-backed job.
- Keep HSM access behind a gateway with its own authorization token and audit log; do not place vendor PINs or private keys in the workflow.
- Run one provider at a time unless investigating cross-provider drift. `all` is useful before releases but consumes every configured environment approval.

## Verification

Local structural checks:

```sh
sh scripts/check-live-kms-security-workflow.shs
bin/simple test test/code_quality/live_kms_security_workflow_spec.spl --mode=interpreter
```

Live provider check:

1. Open GitHub Actions.
2. Select `Live KMS Security Gates`.
3. Run workflow.
4. Select the provider.
5. Approve the matching environment.

The selected job fails before running the Simple spec if required credentials are missing. That prevents a manually selected live lane from silently taking the default skip path.
