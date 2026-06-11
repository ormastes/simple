# Sha1 X4 Specification

> <details>

<!-- sdn-diagram:id=sha1_x4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sha1_x4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sha1_x4_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sha1_x4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha1 X4 Specification

## Scenarios

### sha1_x4 FIPS 180-4 §B.0 — empty string, 4 lanes

#### all 4 lanes of empty input produce da39a3ee...

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: list = []
val result = sha1_x4_message(empty, empty, empty, empty)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
expect(sha1_digest_to_hex(d0)).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
expect(sha1_digest_to_hex(d1)).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
expect(sha1_digest_to_hex(d2)).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
expect(sha1_digest_to_hex(d3)).to_equal("da39a3ee5e6b4b0d3255bfef95601890afd80709")
```

</details>

### sha1_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes

#### all 4 lanes of 'abc' produce a9993e36...

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val abc = [0x61, 0x62, 0x63]
val result = sha1_x4_message(abc, abc, abc, abc)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
expect(sha1_digest_to_hex(d0)).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
expect(sha1_digest_to_hex(d1)).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
expect(sha1_digest_to_hex(d2)).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
expect(sha1_digest_to_hex(d3)).to_equal("a9993e364706816aba3e25717850c26c9cd0d89d")
```

</details>

### sha1_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes

#### all 4 lanes of 56-byte NIST input produce 84983e44...

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = _nist_56_byte()
val result = sha1_x4_message(m, m, m, m)
val d0 = result.get(0)
val d1 = result.get(1)
val d2 = result.get(2)
val d3 = result.get(3)
expect(sha1_digest_to_hex(d0)).to_equal("84983e441c3bd26ebaae4aa1f95129e5e54670f1")
expect(sha1_digest_to_hex(d1)).to_equal("84983e441c3bd26ebaae4aa1f95129e5e54670f1")
expect(sha1_digest_to_hex(d2)).to_equal("84983e441c3bd26ebaae4aa1f95129e5e54670f1")
expect(sha1_digest_to_hex(d3)).to_equal("84983e441c3bd26ebaae4aa1f95129e5e54670f1")
```

</details>

### sha1_x4 lane independence — 4 different inputs

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
val result = sha1_x4_message(m0, m1, m2, m3)
val d0 = sha1_digest_to_hex(result.get(0))
val d1 = sha1_digest_to_hex(result.get(1))
val d2 = sha1_digest_to_hex(result.get(2))
val d3 = sha1_digest_to_hex(result.get(3))
# All four digests must differ (lane independence)
expect(d0 != d1).to_equal(true)
expect(d0 != d2).to_equal(true)
expect(d0 != d3).to_equal(true)
expect(d1 != d2).to_equal(true)
expect(d1 != d3).to_equal(true)
expect(d2 != d3).to_equal(true)
```

</details>

### sha1_x4 regression vs scalar sha1_bytes

#### x4 lane results match sha1_bytes scalar for same 4 inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m0: list = []
val m1 = [0x61, 0x62, 0x63]
val m2 = [0x61]
val m3 = [0x62, 0x63]
val result = sha1_x4_message(m0, m1, m2, m3)
val s0 = sha1_bytes(m0)
val s1 = sha1_bytes(m1)
val s2 = sha1_bytes(m2)
val s3 = sha1_bytes(m3)
expect(_list_eq(result.get(0), s0)).to_equal(true)
expect(_list_eq(result.get(1), s1)).to_equal(true)
expect(_list_eq(result.get(2), s2)).to_equal(true)
expect(_list_eq(result.get(3), s3)).to_equal(true)
```

</details>

### sha1_x4 zero-block first lane

#### lane 0 matches sha1_bytes of zero-block; others match scalar independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero_block = _make_repeat(0, 10)   # 10 zero bytes
val m1 = [0x61, 0x62, 0x63]            # "abc"
val m2 = [0x64, 0x65, 0x66]            # "def"
val m3 = [0x67, 0x68, 0x69]            # "ghi"
val result = sha1_x4_message(zero_block, m1, m2, m3)
val expected0 = sha1_bytes(zero_block)
val expected1 = sha1_bytes(m1)
val expected2 = sha1_bytes(m2)
val expected3 = sha1_bytes(m3)
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
| Source | `test/01_unit/lib/crypto/sha1_x4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sha1_x4 FIPS 180-4 §B.0 — empty string, 4 lanes
- sha1_x4 FIPS 180-4 §B.1 — 'abc', 4 lanes
- sha1_x4 FIPS 180-4 §B.2 — 56-byte input, 4 lanes
- sha1_x4 lane independence — 4 different inputs
- sha1_x4 regression vs scalar sha1_bytes
- sha1_x4 zero-block first lane

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
