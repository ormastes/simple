# Base58 Specification

> <details>

<!-- sdn-diagram:id=base58_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=base58_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

base58_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=base58_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Base58 Specification

## Scenarios

### Base58 encode

#### empty input encodes to empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_empty()).to_equal("")
```

</details>

#### single zero byte encodes to '1'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_zero_one()).to_equal("1")
```

</details>

#### three zero bytes encode to '111'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_zero_three()).to_equal("111")
```

</details>

#### [0x00, 0x00, 0x01] encodes to '112'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_zero_zero_one()).to_equal("112")
```

</details>

#### [0x61] encodes to '2g'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_0x61()).to_equal("2g")
```

</details>

#### Hello World! encodes to '2NEpo7TZRRrLZSi2U'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_enc_hello_world()).to_equal("2NEpo7TZRRrLZSi2U")
```

</details>

### Base58 decode

#### empty string decodes to empty bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_empty_ok()).to_equal(true)
```

</details>

#### '1' decodes to [0x00]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_one_ok()).to_equal(true)
```

</details>

#### '2g' decodes to [0x61]

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_two_g()).to_equal(true)
```

</details>

#### excluded chars 0OIl return InvalidChar

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_dec_invalid_char_0()).to_equal(true)
```

</details>

### Base58Check

#### canonical P2PKH address encodes correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_encode_p2pkh()).to_equal("16UwLL9Risc3QfPqBUvKofHmBQ7wMtjvM")
```

</details>

#### canonical P2PKH address decodes with version 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_decode_p2pkh_ok()).to_equal(true)
```

</details>

#### canonical P2PKH payload is 20 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_decode_p2pkh_payload_len()).to_equal(20)
```

</details>

#### mutated last char returns InvalidChecksum

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_decode_bad_checksum()).to_equal(true)
```

</details>

#### base58check round-trip is lossless

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_roundtrip()).to_equal(true)
```

</details>

#### base58check propagates InvalidChar from bad input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_check_invalid_char_error()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/base58_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Base58 encode
- Base58 decode
- Base58Check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
