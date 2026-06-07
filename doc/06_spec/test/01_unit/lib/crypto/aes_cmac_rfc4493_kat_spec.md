# Aes Cmac Rfc4493 Kat Specification

> <details>

<!-- sdn-diagram:id=aes_cmac_rfc4493_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aes_cmac_rfc4493_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aes_cmac_rfc4493_kat_spec -> std
aes_cmac_rfc4493_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aes_cmac_rfc4493_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aes Cmac Rfc4493 Kat Specification

## Scenarios

### AES-128-CMAC RFC 4493 §2.3 subkey generation

#### K1 matches RFC 4493 §4 reference (fbeed618…)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (k1, _) = aes128_cmac_subkeys(_rfc4493_key())
expect(k1).to_equal(_expected_K1())
```

</details>

#### K2 matches RFC 4493 §4 reference (f7ddac30…)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, k2) = aes128_cmac_subkeys(_rfc4493_key())
expect(k2).to_equal(_expected_K2())
```

</details>

### AES-128-CMAC RFC 4493 §4 generation vectors

#### Example 1: Mlen=0 → bb1d6929 e9593728 7fa37d12 9b756746

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Empty message exercises the K2 (partial-block) path.
expect(aes128_cmac_compute(_rfc4493_key(), _msg_empty())).to_equal(_tag_empty())
```

</details>

#### Example 2: Mlen=16 → 070a16b4 6b4d4144 f79bdd9d d04a287c

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Single full block exercises the K1 (full-block) path.
expect(aes128_cmac_compute(_rfc4493_key(), _msg_16())).to_equal(_tag_16())
```

</details>

#### Example 3: Mlen=40 → dfa66747 de9ae630 30ca3261 1497c827

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 40 = 2 full blocks + 8-byte partial; exercises the K2 path with
# a non-empty partial last block.
expect(aes128_cmac_compute(_rfc4493_key(), _msg_40())).to_equal(_tag_40())
```

</details>

#### Example 4: Mlen=64 → 51f0bebf 7e3b9d92 fc497417 79363cfe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 4 full blocks; exercises the K1 path with multiple CBC-MAC iterations.
expect(aes128_cmac_compute(_rfc4493_key(), _msg_64())).to_equal(_tag_64())
```

</details>

### AES-128-CMAC RFC 4493 §2.5 verification

#### verify accepts the correct tag for each §4 example

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(aes128_cmac_verify(_rfc4493_key(), _msg_empty(), _tag_empty())).to_equal(true)
expect(aes128_cmac_verify(_rfc4493_key(), _msg_16(), _tag_16())).to_equal(true)
expect(aes128_cmac_verify(_rfc4493_key(), _msg_40(), _tag_40())).to_equal(true)
expect(aes128_cmac_verify(_rfc4493_key(), _msg_64(), _tag_64())).to_equal(true)
```

</details>

#### verify rejects a single-bit-flipped tag (CT-compare property)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Even one bit's difference from the correct tag must cause rejection.
# Constant-time XOR-OR accumulator must catch this, not early-exit.
expect(aes128_cmac_verify(_rfc4493_key(), _msg_empty(), _tag_empty_bit_flipped())).to_equal(false)
```

</details>

#### verify rejects a length-mismatched (truncated) tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# An 8-byte tag is half-length; the length check must reject up-front.
expect(aes128_cmac_verify(_rfc4493_key(), _msg_empty(), _tag_short())).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/aes_cmac_rfc4493_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AES-128-CMAC RFC 4493 §2.3 subkey generation
- AES-128-CMAC RFC 4493 §4 generation vectors
- AES-128-CMAC RFC 4493 §2.5 verification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
