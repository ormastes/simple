# Aes Ctr Nist Specification

> <details>

<!-- sdn-diagram:id=aes_ctr_nist_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes_ctr_nist_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes_ctr_nist_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes_ctr_nist_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Ctr Nist Specification

## Scenarios

### AES-CTR NIST SP 800-38A Appendix F.5 vectors

#### F.5.1 AES-128-CTR encrypts 4-block plaintext correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes_ctr_encrypt(_plaintext_f5(), _key_aes128(), _iv_f5())
expect(ct).to_equal(_expected_ct_aes128())
```

</details>

#### F.5.2 AES-128-CTR decrypts back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes_ctr_decrypt(_expected_ct_aes128(), _key_aes128(), _iv_f5())
expect(pt).to_equal(_plaintext_f5())
```

</details>

#### F.5.5 AES-256-CTR encrypts 4-block plaintext correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ct = aes_ctr_encrypt(_plaintext_f5(), _key_aes256(), _iv_f5())
expect(ct).to_equal(_expected_ct_aes256())
```

</details>

#### F.5.6 AES-256-CTR decrypts back to plaintext

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pt = aes_ctr_decrypt(_expected_ct_aes256(), _key_aes256(), _iv_f5())
expect(pt).to_equal(_plaintext_f5())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes_ctr_nist_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-CTR NIST SP 800-38A Appendix F.5 vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
