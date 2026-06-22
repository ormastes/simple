# Live Kms Transport Specification

> <details>

<!-- sdn-diagram:id=live_kms_transport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=live_kms_transport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

live_kms_transport_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=live_kms_transport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Live Kms Transport Specification

## Scenarios

### live KMS transport coverage

#### AWS KMS sign executes only when explicitly enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_ok_or_skipped(_aws_live_sign_status())).to_equal(true)
```

</details>

#### GCP Cloud KMS sign executes only when explicitly enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_ok_or_skipped(_gcp_live_sign_status())).to_equal(true)
```

</details>

#### Azure Key Vault sign executes only when explicitly enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_ok_or_skipped(_azure_live_sign_status())).to_equal(true)
```

</details>

#### PKCS11 HSM gateway sign executes only when explicitly enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_ok_or_skipped(_hsm_live_sign_status())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/security/live_kms_transport_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- live KMS transport coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
