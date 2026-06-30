# Bip39 Kat Specification

> <details>

<!-- sdn-diagram:id=bip39_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bip39_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bip39_kat_spec -> std
bip39_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bip39_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bip39 Kat Specification

## Scenarios

### BIP-39 entropy_to_mnemonic

#### TV1 00..00 (128-bit) → abandon×11 + about

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bip39_entropy_to_mnemonic(_tv1_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv1_mnemonic())
```

</details>

#### TV2 7f..7f → legal winner thank year wave sausage worth useful legal winner thank yellow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bip39_entropy_to_mnemonic(_tv2_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv2_mnemonic())
```

</details>

#### TV3 80..80 → letter advice cage absurd amount doctor acoustic avoid letter advice cage above

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bip39_entropy_to_mnemonic(_tv3_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv3_mnemonic())
```

</details>

#### TV4 ff..ff → zoo×11 + wrong

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bip39_entropy_to_mnemonic(_tv4_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv4_mnemonic())
```

</details>

#### TV5 000..00 (192-bit) → 18 words starting with abandon×17 + agent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bip39_entropy_to_mnemonic(_tv5_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv5_mnemonic())
```

</details>

#### TV6 000..00 (256-bit) → 24 words starting with abandon×23 + art

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bip39_entropy_to_mnemonic(_tv6_entropy())
expect(result.is_ok()).to_equal(true)
expect(result.unwrap()).to_equal(_tv6_mnemonic())
```

</details>

#### invalid entropy length (15 bytes) → Err(InvalidEntropyLength)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad: [u8] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
val result = bip39_entropy_to_mnemonic(bad)
expect(result.is_err()).to_equal(true)
```

</details>

### BIP-39 mnemonic_to_entropy (round-trip)

#### TV1 round-trip: mnemonic_to_entropy(entropy_to_mnemonic(e)) == e

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = bip39_entropy_to_mnemonic(_tv1_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("00000000000000000000000000000000")
```

</details>

#### TV2 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = bip39_entropy_to_mnemonic(_tv2_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f7f")
```

</details>

#### TV3 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = bip39_entropy_to_mnemonic(_tv3_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("80808080808080808080808080808080")
```

</details>

#### TV4 round-trip (zoo×11 + wrong)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dec = bip39_mnemonic_to_entropy(_tv4_mnemonic())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("ffffffffffffffffffffffffffffffff")
```

</details>

#### TV5 round-trip (192-bit)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = bip39_entropy_to_mnemonic(_tv5_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("000000000000000000000000000000000000000000000000")
```

</details>

#### TV6 round-trip (256-bit)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enc = bip39_entropy_to_mnemonic(_tv6_entropy())
val dec = bip39_mnemonic_to_entropy(enc.unwrap())
expect(dec.is_ok()).to_equal(true)
expect(_bytes_hex(dec.unwrap())).to_equal("0000000000000000000000000000000000000000000000000000000000000000")
```

</details>

### BIP-39 error cases

#### unknown word → Err(UnknownWord)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bip39_mnemonic_to_entropy("abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon notaword")
expect(result.is_err()).to_equal(true)
```

</details>

#### invalid checksum → Err(InvalidChecksum)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Flip last word: 'about' (correct for 00..00) → 'ability' (wrong checksum)
val result = bip39_mnemonic_to_entropy("abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon ability")
expect(result.is_err()).to_equal(true)
```

</details>

#### wrong word count (11 words) → Err(InvalidWordCount)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bip39_mnemonic_to_entropy("abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon")
expect(result.is_err()).to_equal(true)
```

</details>

### BIP-39 mnemonic_to_seed

#### TV1 seed with passphrase TREZOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = bip39_mnemonic_to_seed(_tv1_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)
expect(_bytes_hex(seed)).to_equal(_tv1_seed())
```

</details>

#### TV2 seed with passphrase TREZOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = bip39_mnemonic_to_seed(_tv2_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)
expect(_bytes_hex(seed)).to_equal(_tv2_seed())
```

</details>

#### TV3 seed with passphrase TREZOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = bip39_mnemonic_to_seed(_tv3_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)
expect(_bytes_hex(seed)).to_equal(_tv3_seed())
```

</details>

#### seed output is always 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = bip39_mnemonic_to_seed(_tv4_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)
```

</details>

#### empty passphrase gives different seed than TREZOR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed_empty = bip39_mnemonic_to_seed(_tv1_mnemonic(), "")
val seed_trezor = bip39_mnemonic_to_seed(_tv1_mnemonic(), "TREZOR")
expect(_bytes_hex(seed_empty) == _bytes_hex(seed_trezor)).to_equal(false)
```

</details>

#### seed length is 64 bytes for 256-bit entropy mnemonic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = bip39_mnemonic_to_seed(_tv6_mnemonic(), "TREZOR")
expect(seed.len()).to_equal(64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/bip39_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BIP-39 entropy_to_mnemonic
- BIP-39 mnemonic_to_entropy (round-trip)
- BIP-39 error cases
- BIP-39 mnemonic_to_seed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
