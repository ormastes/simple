# Salsa20 Simd Specification

> <details>

<!-- sdn-diagram:id=salsa20_simd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=salsa20_simd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

salsa20_simd_spec -> std
salsa20_simd_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=salsa20_simd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Salsa20 Simd Specification

## Scenarios

### salsa20_8_core scalar — RFC 7914 §B.1

#### scalar: RFC 7914 §B.1 vector matches byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = salsa20_8_core(_rfc_input())
expect(_list_hex(out)).to_equal(_rfc_expected_hex())
```

</details>

#### scalar: output length is 64 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = salsa20_8_core(_rfc_input())
expect(out.len()).to_equal(64)
```

</details>

### salsa20_8_core_x4 SIMD — RFC 7914 §B.1 (lane 0)

#### x4 lane 0: RFC 7914 §B.1 vector matches byte-exact

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Feed the RFC input in lane 0; the other 3 lanes receive distinct data.
val out256 = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
val lane0_hex = _list_hex_range(out256, 0, 64)
expect(lane0_hex).to_equal(_rfc_expected_hex())
```

</details>

#### x4 output is 256 bytes total

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out256 = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(out256.len()).to_equal(256)
```

</details>

### salsa20_8_core_x4 SIMD — parity with scalar on all 4 lanes

#### x4 lane 0 == scalar(_rfc_input)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar0 = salsa20_8_core(_rfc_input())
val out256  = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(_list_hex_range(out256, 0, 64)).to_equal(_list_hex(scalar0))
```

</details>

#### x4 lane 1 == scalar(_alt_input)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar1 = salsa20_8_core(_alt_input())
val out256  = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(_list_hex_range(out256, 64, 128)).to_equal(_list_hex(scalar1))
```

</details>

#### x4 lane 2 == scalar(_incr_input)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar2 = salsa20_8_core(_incr_input())
val out256  = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(_list_hex_range(out256, 128, 192)).to_equal(_list_hex(scalar2))
```

</details>

#### x4 lane 3 == scalar(_fill_input(0x42))

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar3 = salsa20_8_core(_fill_input(0x42))
val out256  = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
expect(_list_hex_range(out256, 192, 256)).to_equal(_list_hex(scalar3))
```

</details>

### salsa20_8_core_x4 SIMD — lane independence

#### all 4 lane outputs are distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out256 = salsa20_8_core_x4(_rfc_input(), _alt_input(), _incr_input(), _fill_input(0x42))
val h0 = _list_hex_range(out256, 0,   64)
val h1 = _list_hex_range(out256, 64,  128)
val h2 = _list_hex_range(out256, 128, 192)
val h3 = _list_hex_range(out256, 192, 256)
# h0 != h1 != h2 != h3 (pairwise inequalities)
expect(h0 == h1).to_equal(false)
expect(h0 == h2).to_equal(false)
expect(h0 == h3).to_equal(false)
expect(h1 == h2).to_equal(false)
expect(h1 == h3).to_equal(false)
expect(h2 == h3).to_equal(false)
```

</details>

### salsa20_8_core_x4 SIMD — zero-block consistency

#### x4 with 4 identical zero inputs: all 4 lanes equal the scalar zero output

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scalar_zero = salsa20_8_core(_zero_input())
val out256 = salsa20_8_core_x4(_zero_input(), _zero_input(), _zero_input(), _zero_input())
val expected = _list_hex(scalar_zero)
expect(_list_hex_range(out256, 0,   64)).to_equal(expected)
expect(_list_hex_range(out256, 64,  128)).to_equal(expected)
expect(_list_hex_range(out256, 128, 192)).to_equal(expected)
expect(_list_hex_range(out256, 192, 256)).to_equal(expected)
```

</details>

### scrypt RFC 7914 §11 V1 — regression after SIMD addition

#### V1: P=\

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = scrypt(_empty_u8(), _empty_u8(), 16, 1, 1, 64)
expect(_bytes_hex(out)).to_equal(
    "77d6576238657b203b19ca42c18a0497f16b4844e3074ae8dfdffa3fede21442fcd0069ded0948f8326a753a0fc81f17e8d3e0fb2e0d3628cf35e20c38d18906"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/salsa20_simd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- salsa20_8_core scalar — RFC 7914 §B.1
- salsa20_8_core_x4 SIMD — RFC 7914 §B.1 (lane 0)
- salsa20_8_core_x4 SIMD — parity with scalar on all 4 lanes
- salsa20_8_core_x4 SIMD — lane independence
- salsa20_8_core_x4 SIMD — zero-block consistency
- scrypt RFC 7914 §11 V1 — regression after SIMD addition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
