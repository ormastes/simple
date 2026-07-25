# Rsa Pss Smoke Specification

> <details>

<!-- sdn-diagram:id=rsa_pss_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rsa_pss_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rsa_pss_smoke_spec -> std
rsa_pss_smoke_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rsa_pss_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rsa Pss Smoke Specification

## Scenarios

### RSA-PSS module smoke

#### rejects empty SPKI for verify

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rsa_pss_sha256_verify(_empty(), _empty(), _empty())).to_equal(false)
```

</details>

#### rejects empty PKCS8 for sign (returns empty signature)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rsa_pss_sha256_sign(_empty(), _empty(), _empty()).len().to_i64()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `/home/ormastes/dev/pub/simple/test/01_unit/lib/crypto/rsa_pss_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RSA-PSS module smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
