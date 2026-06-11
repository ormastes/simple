# Simd Dispatch Facade Specification

> <details>

<!-- sdn-diagram:id=simd_dispatch_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simd_dispatch_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simd_dispatch_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simd_dispatch_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Dispatch Facade Specification

## Scenarios

### SIMD dispatch facades

### utf8 counting facade

#### preserves mixed-width UTF-8 counting through the public entrypoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = [0x41, 0xE2, 0x82, 0xAC, 0xF0, 0x9F, 0x98, 0x80]
expect(utf8_count_codepoints(bytes)).to_equal(3)
expect(text_codepoint_len("A€😀")).to_equal(3)
```

</details>

### aes block facade

#### preserves the AES-128 encrypt/decrypt known answer through the public API

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = hex_to_bytes("000102030405060708090a0b0c0d0e0f")
val plaintext = hex_to_bytes("00112233445566778899aabbccddeeff")
val ciphertext = aes_encrypt_block(plaintext, key)
expect(bytes_to_hex(ciphertext)).to_equal("69c4e0d86a7b0430d8cdb78070b4c55a")
expect(aes_decrypt_block(ciphertext, key)).to_equal(plaintext)
```

</details>

#### keeps the expanded-key block helpers wired through the same facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = hex_to_bytes("000102030405060708090a0b0c0d0e0f")
val plaintext = hex_to_bytes("00112233445566778899aabbccddeeff")
val expanded = expand_key(key, 16)
val ciphertext = aes_encrypt_block_with_expanded(plaintext, expanded, 10)
expect(bytes_to_hex(ciphertext)).to_equal("69c4e0d86a7b0430d8cdb78070b4c55a")
expect(aes_decrypt_block_with_expanded(ciphertext, expanded, 10)).to_equal(plaintext)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/simd_dispatch_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SIMD dispatch facades
- utf8 counting facade
- aes block facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
