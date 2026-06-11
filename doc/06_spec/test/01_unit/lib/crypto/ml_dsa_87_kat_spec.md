# Ml Dsa 87 Kat Specification

> <details>

<!-- sdn-diagram:id=ml_dsa_87_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ml_dsa_87_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ml_dsa_87_kat_spec -> std
ml_dsa_87_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ml_dsa_87_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ml Dsa 87 Kat Specification

## Scenarios

### ML-DSA-87 KeyGen sizes

#### ml_dsa_keygen_87 produces pk of size 2592 bytes (FIPS 204 §B Table 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_keygen_pk_len()).to_equal(2592)
expect(_keygen_pk_len()).to_equal(pk_size_87())
```

</details>

#### ml_dsa_keygen_87 produces sk of size 4896 bytes (FIPS 204 §B Table 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_keygen_sk_len()).to_equal(4896)
expect(_keygen_sk_len()).to_equal(sk_size_87())
```

</details>

### ML-DSA-87 end-to-end Sign + Verify

#### Sign(sk, m) → σ; Verify(pk, m, σ) == true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sign_verify_round_trip()).to_equal(true)
```

</details>

#### Verify rejects bit-flipped message

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_verify_rejects_tampered_msg()).to_equal(true)
```

</details>

#### Verify rejects bit-flipped signature (c_tilde)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_verify_rejects_tampered_sig()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/ml_dsa_87_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ML-DSA-87 KeyGen sizes
- ML-DSA-87 end-to-end Sign + Verify

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
