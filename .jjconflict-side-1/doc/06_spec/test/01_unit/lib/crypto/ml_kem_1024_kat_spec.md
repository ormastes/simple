# Ml Kem 1024 Kat Specification

> <details>

<!-- sdn-diagram:id=ml_kem_1024_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ml_kem_1024_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ml_kem_1024_kat_spec -> std
ml_kem_1024_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ml_kem_1024_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ml Kem 1024 Kat Specification

## Scenarios

### ML-KEM-1024 size invariants (FIPS 203 §8 Table 3)

#### ITEM-1a ek = 1568 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_1024_ek_bytes().to_equal(1568)
```

</details>

#### ITEM-1b dk = 3168 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_1024_dk_bytes().to_equal(3168)
```

</details>

#### ITEM-1c ciphertext = 1568 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_1024_ct_bytes().to_equal(1568)
```

</details>

#### ITEM-1d shared secret = 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_1024_ss_bytes().to_equal(32)
```

</details>

### ML-KEM-1024 parameter table (FIPS 203 §2.3 Table 2)

#### ITEM-2a k = 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_k_1024().to_equal(4)
```

</details>

#### ITEM-2b η1 = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_eta1_1024().to_equal(2)
```

</details>

#### ITEM-2c η2 = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_eta2_1024().to_equal(2)
```

</details>

#### ITEM-2d du = 11

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_du_1024().to_equal(11)
```

</details>

#### ITEM-2e dv = 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_dv_1024().to_equal(5)
```

</details>

#### ITEM-2f q = 3329 (shared)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ml_kem_q().to_equal(3329)
```

</details>

### ML-KEM-1024 deterministic round-trip (top-level harness)

#### ITEM-3 KeyGen + Encaps + Decaps round-trip with d = z = m = 0^32

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The actual round-trip computation runs at file load via
# `ml_kem_1024_round_trip_check()`. This `it` block records the
# outcome flag; if loading succeeded with a wrong shared secret,
# the flag is 0 and this assertion fails.
ml_kem_1024_round_trip_ok.to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `/home/ormastes/dev/pub/simple/test/01_unit/lib/crypto/ml_kem_1024_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ML-KEM-1024 size invariants (FIPS 203 §8 Table 3)
- ML-KEM-1024 parameter table (FIPS 203 §2.3 Table 2)
- ML-KEM-1024 deterministic round-trip (top-level harness)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
