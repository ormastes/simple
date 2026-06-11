# Sha256 X4 Specification

> <details>

<!-- sdn-diagram:id=sha256_x4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha256_x4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha256_x4_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha256_x4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha256 X4 Specification

## Scenarios

### sha256_x4 FIPS 180-4 §B.1 — empty string, 4 lanes

#### all 4 lanes of empty input produce e3b0c442...

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: list = []
val result = sha256_x4_message(empty, empty, empty, empty)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
val expected = "e3b0c44298fc1c149afbf4c8996fb924" + "27ae41e4649b934ca495991b7852b855"
expect(sha256_digest_to_hex(d0)).to_equal(expected)
expect(sha256_digest_to_hex(d1)).to_equal(expected)
expect(sha256_digest_to_hex(d2)).to_equal(expected)
expect(sha256_digest_to_hex(d3)).to_equal(expected)
```

</details>

### sha256_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes

#### all 4 lanes of 'abc' produce ba7816bf...

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val abc = [0x61, 0x62, 0x63]
val result = sha256_x4_message(abc, abc, abc, abc)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
val expected = "ba7816bf8f01cfea414140de5dae2223" + "b00361a396177a9cb410ff61f20015ad"
expect(sha256_digest_to_hex(d0)).to_equal(expected)
expect(sha256_digest_to_hex(d1)).to_equal(expected)
expect(sha256_digest_to_hex(d2)).to_equal(expected)
expect(sha256_digest_to_hex(d3)).to_equal(expected)
```

</details>

### sha256_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes

#### all 4 lanes of 56-byte NIST input produce 248d6a61...

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = _nist_56_byte()
val result = sha256_x4_message(m, m, m, m)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
val expected = "248d6a61d20638b8e5c026930c3e6039" + "a33ce45964ff2167f6ecedd419db06c1"
expect(sha256_digest_to_hex(d0)).to_equal(expected)
expect(sha256_digest_to_hex(d1)).to_equal(expected)
expect(sha256_digest_to_hex(d2)).to_equal(expected)
expect(sha256_digest_to_hex(d3)).to_equal(expected)
```

</details>

### sha256_x4 lane independence — 4 different inputs

#### 4 distinct inputs produce 4 distinct digests

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m0: list = []                         # empty
val m1 = [0x61, 0x62, 0x63]              # "abc"
val m2 = [0x61]                           # "a"
val m3 = [0x62, 0x63]                     # "bc"
val result = sha256_x4_message(m0, m1, m2, m3)
val d0 = sha256_digest_to_hex(result.get(0))
val d1 = sha256_digest_to_hex(result.get(1))
val d2 = sha256_digest_to_hex(result.get(2))
val d3 = sha256_digest_to_hex(result.get(3))
# All four digests must differ (lane independence)
expect(d0 != d1).to_equal(true)
expect(d0 != d2).to_equal(true)
expect(d0 != d3).to_equal(true)
expect(d1 != d2).to_equal(true)
expect(d1 != d3).to_equal(true)
expect(d2 != d3).to_equal(true)
```

</details>

### sha256_x4 regression vs scalar sha256_bytes

#### x4 lane results match sha256_bytes scalar for same 4 inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m0: list = []
val m1 = [0x61, 0x62, 0x63]
val m2 = [0x61]
val m3 = [0x62, 0x63]
val result = sha256_x4_message(m0, m1, m2, m3)
val s0 = sha256_bytes(m0)
val s1 = sha256_bytes(m1)
val s2 = sha256_bytes(m2)
val s3 = sha256_bytes(m3)
expect(_list_eq(result.get(0), s0)).to_equal(true)
expect(_list_eq(result.get(1), s1)).to_equal(true)
expect(_list_eq(result.get(2), s2)).to_equal(true)
expect(_list_eq(result.get(3), s3)).to_equal(true)
```

</details>

### sha256_x4 pre-padded single block — boundary test

#### sha256_x4 of manually padded 'abc' block matches sha256_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SHA-256 pad of "abc" (3 bytes) -> exactly 64 bytes
# abc = [0x61, 0x62, 0x63], then 0x80, zeros to 56 bytes, then 64-bit big-endian 24
val abc = [0x61, 0x62, 0x63]
val padded_abc = _sha256_pad_for_test(abc)
val result = sha256_x4(padded_abc, padded_abc, padded_abc, padded_abc)
val d0 = result.get(0)
val d1 = result.get(1)
val expected = sha256_bytes(abc)
expect(_list_eq(d0, expected)).to_equal(true)
expect(_list_eq(d1, expected)).to_equal(true)
```

</details>

### sha256_x4 regression — diverse inputs match scalar

#### zero-block, 'def', 'ghi', 10-zero-bytes all match scalar

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero_block = _make_repeat(0, 10)
val m1 = [0x64, 0x65, 0x66]   # "def"
val m2 = [0x67, 0x68, 0x69]   # "ghi"
val m3 = [0x61, 0x62, 0x63, 0x64]  # "abcd"
val result = sha256_x4_message(zero_block, m1, m2, m3)
val expected0 = sha256_bytes(zero_block)
val expected1 = sha256_bytes(m1)
val expected2 = sha256_bytes(m2)
val expected3 = sha256_bytes(m3)
expect(_list_eq(result.get(0), expected0)).to_equal(true)
expect(_list_eq(result.get(1), expected1)).to_equal(true)
expect(_list_eq(result.get(2), expected2)).to_equal(true)
expect(_list_eq(result.get(3), expected3)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/sha256_x4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sha256_x4 FIPS 180-4 §B.1 — empty string, 4 lanes
- sha256_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes
- sha256_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes
- sha256_x4 lane independence — 4 different inputs
- sha256_x4 regression vs scalar sha256_bytes
- sha256_x4 pre-padded single block — boundary test
- sha256_x4 regression — diverse inputs match scalar

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
