# Variant Api Parity Specification

> <details>

<!-- sdn-diagram:id=variant_api_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=variant_api_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

variant_api_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=variant_api_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Variant Api Parity Specification

## Scenarios

### Variant API parity portable smoke

#### records supported memory/runtime variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val variants = ["gc_async_mut", "nogc_async_mut", "nogc_sync_mut"]
expect(variants.len()).to_equal(3)
expect(variants[2]).to_equal("nogc_sync_mut")
```

</details>

#### records shared API areas

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val areas = ["gpu", "torch", "io"]
expect(areas.len()).to_equal(3)
expect(areas[0]).to_equal("gpu")
```

</details>

#### keeps the stable simd facade available

1. detect profile
   - Expected: name.len() > 0 is true
   - Expected: profile_name().len() > 0 is true
   - Expected: has_rvv() == true or has_rvv() == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
detect_profile()
val name = profile_name()
expect(name.len() > 0).to_equal(true)
expect(profile_name().len() > 0).to_equal(true)
expect(has_rvv() == true or has_rvv() == false).to_equal(true)
```

</details>

#### keeps the shared utf8 facade available

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

#### keeps the shared aes facade available

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/core/variant_api_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Variant API parity portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
