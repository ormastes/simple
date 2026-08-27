# Live KMS Security Workflow Canary

> Guards the manually-triggered credentialed live KMS CI lane.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Guards the manually-triggered credentialed live KMS CI lane.

## Scenarios

### live KMS security workflow

#### is manual-only and exposes provider selection

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is manual-only and exposes provider selection
   - Expected: workflow contains `workflow_dispatch:`
   - Expected: workflow contains `contents: read`
   - Expected: workflow contains `id-token: write`
   - Expected: workflow contains `provider:`
   - Expected: workflow contains `auth:`
   - Expected: workflow contains `- aws`
   - Expected: workflow contains `- gcp`
   - Expected: workflow contains `- azure`
   - Expected: workflow contains `- hsm`
   - Expected: workflow contains `- all`
   - Expected: workflow contains `- secret`
   - Expected: workflow contains `- oidc`
   - Expected: workflow does not contain `push:`
   - Expected: workflow does not contain `pull_request:`
   - Expected: workflow does not contain `schedule:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is manual-only and exposes provider selection")
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

- runs the live KMS integration spec for every provider job
   - Expected: workflow contains `aws-live-kms:`
   - Expected: workflow contains `gcp-live-kms:`
   - Expected: workflow contains `azure-live-kms:`
   - Expected: workflow contains `hsm-live-kms:`
   - Expected: workflow contains `environment: live-kms-aws`
   - Expected: workflow contains `environment: live-kms-gcp`
   - Expected: workflow contains `environment: live-kms-azure`
   - Expected: workflow contains `environment: live-kms-hsm`
   - Expected: workflow contains `test/integration/lib/security/live_kms_transport_spec.spl`
   - Expected: workflow contains `SIMPLE_LIB=src`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the live KMS integration spec for every provider job")
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

- wires the credential secrets required by the live KMS spec
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AWS_ENDPOINT`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AWS_KEY_ID`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AWS_AUTHORIZATION`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AWS_OIDC_ROLE_ARN`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AWS_REGION`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AWS_AMZ_DATETIME`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AUTH`
   - Expected: workflow contains `inputs.auth`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_GCP_ENDPOINT`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_GCP_KEY_VERSION`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_GCP_BEARER`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_GCP_WORKLOAD_IDENTITY_PROVIDER`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_GCP_SERVICE_ACCOUNT`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AZURE_VAULT`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AZURE_KEY`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AZURE_BEARER`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AZURE_CLIENT_ID`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AZURE_TENANT_ID`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AZURE_SUBSCRIPTION_ID`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_HSM_ENDPOINT`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_HSM_SLOT`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_HSM_KEY`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_HSM_AUTHORIZATION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wires the credential secrets required by the live KMS spec")
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

- supports OIDC bootstrap for cloud provider lanes
   - Expected: workflow contains `aws-actions/configure-aws-credentials@v4`
   - Expected: workflow contains `aws sts get-caller-identity`
   - Expected: workflow contains `AWS_SESSION_TOKEN`
   - Expected: workflow contains `SIMPLE_LIVE_KMS_AWS_AMZ_DATETIME=$(date -u +%Y%m%dT%H%M%SZ)`
   - Expected: workflow does not contain `until SigV4 runtime signing lands`
   - Expected: workflow contains `google-github-actions/auth@v2`
   - Expected: workflow contains `token_format: access_token`
   - Expected: workflow contains `Export GCP OIDC bearer`
   - Expected: workflow contains `azure/login@v2`
   - Expected: workflow contains `az account get-access-token --resource https://vault.azure.net`
   - Expected: workflow contains `Export Azure OIDC bearer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports OIDC bootstrap for cloud provider lanes")
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

- fails selected provider jobs before the spec can skip missing credentials
   - Expected: workflow contains `Require AWS live KMS credentials`
   - Expected: workflow contains `Require GCP live KMS credentials`
   - Expected: workflow contains `Require Azure live KMS credentials`
   - Expected: workflow contains `Require HSM live KMS credentials`
   - Expected: workflow contains `::error::$name is required`
   - Expected: workflow contains `exit "$missing"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails selected provider jobs before the spec can skip missing credentials")
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

- has an operator guide for protected environments and local checks
   - Expected: guide contains `live-kms-aws`
   - Expected: guide contains `live-kms-gcp`
   - Expected: guide contains `live-kms-azure`
   - Expected: guide contains `live-kms-hsm`
   - Expected: guide contains `scripts/check/check-live-kms-security-workflow.shs`
   - Expected: guide contains `workflow_dispatch`
   - Expected: guide contains `OIDC`
   - Expected: guide contains `SIMPLE_LIVE_KMS_GCP_WORKLOAD_IDENTITY_PROVIDER`
   - Expected: guide contains `SIMPLE_LIVE_KMS_AZURE_CLIENT_ID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has an operator guide for protected environments and local checks")
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

- is enforced by the repository hygiene gate
   - Expected: hygiene contains `scripts/check/check-live-kms-security-workflow.shs`
   - Expected: hygiene contains `live KMS workflow invariant check failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is enforced by the repository hygiene gate")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `be914ed49de43a494e610316a0e5bb3d22dfd4576fad032acba0287a9f064575`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be914ed49de43a494e610316a0e5bb3d22dfd4576fad032acba0287a9f064575`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be914ed49de43a494e610316a0e5bb3d22dfd4576fad032acba0287a9f064575`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/quality/code_quality/live_kms_security_workflow_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/live_kms_security_workflow_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/live_kms_security_workflow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/live_kms_security_workflow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/live_kms_security_workflow_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is manual-only and exposes provider selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/live_kms_security_workflow_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the live KMS integration spec for every provider job' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/live_kms_security_workflow_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wires the credential secrets required by the live KMS spec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
