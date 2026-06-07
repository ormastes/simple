# Ml Dsa 65 Specification

> <details>

<!-- sdn-diagram:id=ml_dsa_65_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ml_dsa_65_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ml_dsa_65_spec -> std
ml_dsa_65_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ml_dsa_65_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ml Dsa 65 Specification

## Scenarios

### ML-DSA-65 NTT and ring primitives

#### NTT round-trip preserves coefficient-domain polynomial

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_ntt_round_trip_ok()).to_equal(true)
```

</details>

#### NTT([1, 0, ..., 0]) == [1; 256] (zetas table validation)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_ntt_constant_poly_ok()).to_equal(true)
```

</details>

#### NTT pointwise multiplication equals coefficient-domain convolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_ntt_pointwise_matches_direct_ok()).to_equal(true)
```

</details>

#### X^255 * X = -1 mod (X^256 + 1) via NTT

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_ntt_negacyclic_boundary()).to_equal(ml_dsa_q() - 1)
```

</details>

### ML-DSA-65 Power2Round + Decompose

#### Power2Round(r) recovers r1 * 2^13 + r0 == r

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = power2round_int(1234567)
expect(pair[0] * 8192 + pair[1]).to_equal(1234567)
```

</details>

#### Decompose(r) reconstructs r mod q

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = decompose_int(1234567)
expect(modq(pair[0] * 2 * ml_dsa_gamma2_65() + pair[1])).to_equal(1234567)
```

</details>

#### Decompose r1 lies in [0, 16) for q=8380417 over 200 samples

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_decompose_r1_min() >= 0).to_equal(true)
expect(_decompose_r1_max() <= 15).to_equal(true)
```

</details>

### ML-DSA-65 MakeHint / UseHint

#### UseHint(MakeHint(z, r), r+z) recovers HighBits(r) for 50 samples

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_make_use_hint_failures()).to_equal(0)
```

</details>

### ML-DSA-65 BitPack round-trip

#### SimpleBitPack at 10 bits packs 256 coefficients to 320 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bitpack_size(10)).to_equal(320)
```

</details>

#### SimpleBitPack at 10 bits round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bitpack_roundtrip_ok(10)).to_equal(true)
```

</details>

#### SimpleBitPack at 4 bits packs 256 coefficients to 128 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bitpack_size(4)).to_equal(128)
```

</details>

#### SimpleBitPack at 4 bits round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bitpack_roundtrip_ok(4)).to_equal(true)
```

</details>

### ML-DSA-65 SHAKE NIST KAT

#### SHAKE-128(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = shake128([], 16)
expect(_hex(out, 16)).to_equal("7f9c2ba4e88f827d616045507605853e")
```

</details>

#### SHAKE-256(\

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = shake256([], 16)
expect(_hex(out, 16)).to_equal("46b9dd2b0ba88d13233b3feb743eeb24")
```

</details>

### ML-DSA-65 SampleInBall

#### produces exactly tau=49 nonzero coefficients

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sample_in_ball_nonzero_count(49)).to_equal(49)
```

</details>

#### all nonzero coefficients are in {-1, +1}

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_sample_in_ball_only_pm1(49)).to_equal(true)
```

</details>

### ML-DSA-65 KeyGen sizes

#### ml_dsa_keygen_65 produces pk of size 1952 bytes (FIPS 204 §B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_keygen_pk_len()).to_equal(1952)
expect(_keygen_pk_len()).to_equal(pk_size_65())
```

</details>

#### ml_dsa_keygen_65 produces sk of size 4032 bytes (FIPS 204 §B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_keygen_sk_len()).to_equal(4032)
expect(_keygen_sk_len()).to_equal(sk_size_65())
```

</details>

### ML-DSA-65 end-to-end Sign + Verify

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
| Source | `test/01_unit/lib/crypto/ml_dsa_65_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ML-DSA-65 NTT and ring primitives
- ML-DSA-65 Power2Round + Decompose
- ML-DSA-65 MakeHint / UseHint
- ML-DSA-65 BitPack round-trip
- ML-DSA-65 SHAKE NIST KAT
- ML-DSA-65 SampleInBall
- ML-DSA-65 KeyGen sizes
- ML-DSA-65 end-to-end Sign + Verify

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
