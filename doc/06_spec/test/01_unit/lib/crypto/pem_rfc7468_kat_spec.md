# Pem Rfc7468 Kat Specification

> <details>

<!-- sdn-diagram:id=pem_rfc7468_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pem_rfc7468_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pem_rfc7468_kat_spec -> std
pem_rfc7468_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pem_rfc7468_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pem Rfc7468 Kat Specification

## Scenarios

### PEM RFC 7468 — SPKI round-trip

#### encode+decode recovers original 32-byte DER

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val der = _der_32()
val label = _label_spki()
val pem_bytes = pem_encode(label, der)
val result = pem_decode(pem_bytes)
expect(result.is_ok()).to_equal(true)
val block = result.unwrap()
expect(_u8_eq(block.der, der)).to_equal(true)
```

</details>

#### encode+decode recovers original label PUBLIC KEY

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val der = _der_32()
val label = _label_spki()
val pem_bytes = pem_encode(label, der)
val result = pem_decode(pem_bytes)
expect(result.is_ok()).to_equal(true)
val block = result.unwrap()
expect(_u8_to_text(block.label)).to_equal("PUBLIC KEY")
```

</details>

#### encoded output starts with -----BEGIN PUBLIC KEY-----

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pem_bytes = pem_encode(_label_spki(), _der_32())
val pem_text = _u8_to_text(pem_bytes)
expect(pem_text.starts_with("-----BEGIN PUBLIC KEY-----")).to_equal(true)
```

</details>

#### encoded output ends with -----END PUBLIC KEY-----\\n

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pem_bytes = pem_encode(_label_spki(), _der_32())
val pem_text = _u8_to_text(pem_bytes)
expect(pem_text.ends_with("-----END PUBLIC KEY-----\n")).to_equal(true)
```

</details>

#### DER length is preserved through round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val der = _der_32()
val pem_bytes = pem_encode(_label_spki(), der)
val result = pem_decode(pem_bytes)
expect(result.is_ok()).to_equal(true)
val block = result.unwrap()
expect(block.der.len().to_i64()).to_equal(32)
```

</details>

### PEM RFC 7468 — multi-block pem_decode_all

#### decodes two concatenated blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pem1 = pem_encode(_label_spki(), _der_32())
val pem2 = pem_encode(_label_cert(), _der_32())
# Concatenate with a separator newline (explanatory text is silently ignored)
val combined_text = _u8_to_text(pem1) + "\n" + _u8_to_text(pem2)
val combined = _text_to_u8(combined_text)
val result = pem_decode_all(combined)
expect(result.is_ok()).to_equal(true)
val blocks = result.unwrap()
expect(blocks.len()).to_equal(2)
```

</details>

#### first block has label PUBLIC KEY

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pem1 = pem_encode(_label_spki(), _der_32())
val pem2 = pem_encode(_label_cert(), _der_32())
val combined_text = _u8_to_text(pem1) + "\n" + _u8_to_text(pem2)
val combined = _text_to_u8(combined_text)
val result = pem_decode_all(combined)
expect(result.is_ok()).to_equal(true)
val blocks = result.unwrap()
val b0: PemBlock = blocks[0]
expect(_u8_to_text(b0.label)).to_equal("PUBLIC KEY")
```

</details>

#### second block has label CERTIFICATE

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pem1 = pem_encode(_label_spki(), _der_32())
val pem2 = pem_encode(_label_cert(), _der_32())
val combined_text = _u8_to_text(pem1) + "\n" + _u8_to_text(pem2)
val combined = _text_to_u8(combined_text)
val result = pem_decode_all(combined)
expect(result.is_ok()).to_equal(true)
val blocks = result.unwrap()
val b1: PemBlock = blocks[1]
expect(_u8_to_text(b1.label)).to_equal("CERTIFICATE")
```

</details>

#### empty input returns Ok with zero blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pem_decode_all(_text_to_u8(""))
expect(result.is_ok()).to_equal(true)
val blocks = result.unwrap()
expect(blocks.len()).to_equal(0)
```

</details>

### PEM RFC 7468 — malformed rejection

#### missing END marker → Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Valid BEGIN but no END
val bad = _text_to_u8("-----BEGIN PUBLIC KEY-----\nYWJj\n")
val result = pem_decode(bad)
expect(result.is_err()).to_equal(true)
```

</details>

#### label mismatch BEGIN CERTIFICATE / END PUBLIC KEY → Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pem_decode requires matching END label
val bad_text = "-----BEGIN CERTIFICATE-----\nYWJj\n-----END PUBLIC KEY-----\n"
val bad = _text_to_u8(bad_text)
val result = pem_decode(bad)
expect(result.is_err()).to_equal(true)
```

</details>

#### no BEGIN marker at all → Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad = _text_to_u8("just some random text with no markers")
val result = pem_decode(bad)
expect(result.is_err()).to_equal(true)
```

</details>

#### empty body → Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# BEGIN + END with no base64 content
val bad_text = "-----BEGIN PUBLIC KEY-----\n-----END PUBLIC KEY-----\n"
val bad = _text_to_u8(bad_text)
val result = pem_decode(bad)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/pem_rfc7468_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PEM RFC 7468 — SPKI round-trip
- PEM RFC 7468 — multi-block pem_decode_all
- PEM RFC 7468 — malformed rejection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
