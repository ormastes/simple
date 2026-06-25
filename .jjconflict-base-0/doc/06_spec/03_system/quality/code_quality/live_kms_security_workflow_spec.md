# Live KMS Security Workflow Canary

> Guards the manually-triggered credentialed live KMS CI lane.

<!-- sdn-diagram:id=live_kms_security_workflow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=live_kms_security_workflow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

live_kms_security_workflow_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=live_kms_security_workflow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Live KMS Security Workflow Canary

Guards the manually-triggered credentialed live KMS CI lane.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/live_kms_security_workflow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Guards the manually-triggered credentialed live KMS CI lane.

## Scenarios

### live KMS security workflow

#### is manual-only and exposes provider selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workflow = rt_file_read_text(WORKFLOW)
expect(workflow.contains("workflow_dispatch:")).to_equal(true)
expect(workflow.contains("contents: read")).to_equal(true)
expect(workflow.contains("id-token: write")).to_equal(true)
expect(workflow.contains("provider:")).to_equal(true)
expect(workflow.contains("auth:")).to_equal(true)
expect(workflow.contains("- aws")).to_equal(true)
expect(workflow.contains("- gcp")).to_equal(true)
expect(workflow.contains("- azure")).to_equal(true)
expect(workflow.contains("- hsm")).to_equal(true)
expect(workflow.contains("- all")).to_equal(true)
expect(workflow.contains("- secret")).to_equal(true)
expect(workflow.contains("- oidc")).to_equal(true)
expect(workflow.contains("push:")).to_equal(false)
expect(workflow.contains("pull_request:")).to_equal(false)
expect(workflow.contains("schedule:")).to_equal(false)
```

</details>

#### runs the live KMS integration spec for every provider job

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workflow = rt_file_read_text(WORKFLOW)
expect(workflow.contains("aws-live-kms:")).to_equal(true)
expect(workflow.contains("gcp-live-kms:")).to_equal(true)
expect(workflow.contains("azure-live-kms:")).to_equal(true)
expect(workflow.contains("hsm-live-kms:")).to_equal(true)
expect(workflow.contains("environment: live-kms-aws")).to_equal(true)
expect(workflow.contains("environment: live-kms-gcp")).to_equal(true)
expect(workflow.contains("environment: live-kms-azure")).to_equal(true)
expect(workflow.contains("environment: live-kms-hsm")).to_equal(true)
expect(workflow.contains("test/integration/lib/security/live_kms_transport_spec.spl")).to_equal(true)
expect(workflow.contains("SIMPLE_LIB=src")).to_equal(true)
```

</details>

#### wires the credential secrets required by the live KMS spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workflow = rt_file_read_text(WORKFLOW)
expect(workflow.contains("SIMPLE_LIVE_KMS_AWS_ENDPOINT")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AWS_KEY_ID")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AWS_AUTHORIZATION")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AWS_OIDC_ROLE_ARN")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AWS_REGION")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AWS_AMZ_DATETIME")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AUTH")).to_equal(true)
expect(workflow.contains("inputs.auth")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_GCP_ENDPOINT")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_GCP_KEY_VERSION")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_GCP_BEARER")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_GCP_WORKLOAD_IDENTITY_PROVIDER")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_GCP_SERVICE_ACCOUNT")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AZURE_VAULT")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AZURE_KEY")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AZURE_BEARER")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AZURE_CLIENT_ID")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AZURE_TENANT_ID")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AZURE_SUBSCRIPTION_ID")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_HSM_ENDPOINT")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_HSM_SLOT")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_HSM_KEY")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_HSM_AUTHORIZATION")).to_equal(true)
```

</details>

#### supports OIDC bootstrap for cloud provider lanes

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workflow = rt_file_read_text(WORKFLOW)
expect(workflow.contains("aws-actions/configure-aws-credentials@v4")).to_equal(true)
expect(workflow.contains("aws sts get-caller-identity")).to_equal(true)
expect(workflow.contains("AWS_SESSION_TOKEN")).to_equal(true)
expect(workflow.contains("SIMPLE_LIVE_KMS_AWS_AMZ_DATETIME=$(date -u +%Y%m%dT%H%M%SZ)")).to_equal(true)
expect(workflow.contains("until SigV4 runtime signing lands")).to_equal(false)
expect(workflow.contains("google-github-actions/auth@v2")).to_equal(true)
expect(workflow.contains("token_format: access_token")).to_equal(true)
expect(workflow.contains("Export GCP OIDC bearer")).to_equal(true)
expect(workflow.contains("azure/login@v2")).to_equal(true)
expect(workflow.contains("az account get-access-token --resource https://vault.azure.net")).to_equal(true)
expect(workflow.contains("Export Azure OIDC bearer")).to_equal(true)
```

</details>

#### fails selected provider jobs before the spec can skip missing credentials

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workflow = rt_file_read_text(WORKFLOW)
expect(workflow.contains("Require AWS live KMS credentials")).to_equal(true)
expect(workflow.contains("Require GCP live KMS credentials")).to_equal(true)
expect(workflow.contains("Require Azure live KMS credentials")).to_equal(true)
expect(workflow.contains("Require HSM live KMS credentials")).to_equal(true)
expect(workflow.contains("::error::$name is required")).to_equal(true)
expect(workflow.contains("exit \"$missing\"")).to_equal(true)
```

</details>

#### has an operator guide for protected environments and local checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guide = rt_file_read_text(GUIDE)
expect(guide.contains("live-kms-aws")).to_equal(true)
expect(guide.contains("live-kms-gcp")).to_equal(true)
expect(guide.contains("live-kms-azure")).to_equal(true)
expect(guide.contains("live-kms-hsm")).to_equal(true)
expect(guide.contains("scripts/check/check-live-kms-security-workflow.shs")).to_equal(true)
expect(guide.contains("workflow_dispatch")).to_equal(true)
expect(guide.contains("OIDC")).to_equal(true)
expect(guide.contains("SIMPLE_LIVE_KMS_GCP_WORKLOAD_IDENTITY_PROVIDER")).to_equal(true)
expect(guide.contains("SIMPLE_LIVE_KMS_AZURE_CLIENT_ID")).to_equal(true)
```

</details>

#### is enforced by the repository hygiene gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hygiene = rt_file_read_text(HYGIENE)
expect(hygiene.contains("scripts/check/check-live-kms-security-workflow.shs")).to_equal(true)
expect(hygiene.contains("live KMS workflow invariant check failed")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
