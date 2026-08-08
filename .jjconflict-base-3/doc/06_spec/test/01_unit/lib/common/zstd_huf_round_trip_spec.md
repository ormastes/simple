# Zstd Huf Round Trip Specification

> <details>

<!-- sdn-diagram:id=zstd_huf_round_trip_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=zstd_huf_round_trip_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

zstd_huf_round_trip_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=zstd_huf_round_trip_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Huf Round Trip Specification

## Scenarios

### zstd huf encoder round-trips the existing decoder

#### round-trips a one-symbol stream via the bounded synthetic tree

-  round trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val literals: [u8] = [
    0x5Au8, 0x5Au8, 0x5Au8, 0x5Au8,
    0x5Au8, 0x5Au8, 0x5Au8, 0x5Au8,
    0x5Au8, 0x5Au8, 0x5Au8, 0x5Au8
]
_round_trip(literals)
```

</details>

#### round-trips a two-symbol stream

-  round trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val literals: [u8] = [
    0x41u8, 0x42u8, 0x41u8, 0x41u8,
    0x42u8, 0x42u8, 0x41u8, 0x42u8
]
_round_trip(literals)
```

</details>

#### round-trips a 4-symbol mixed-length input

-  round trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 'a' x 6, 'b' x 3, 'c' x 2, 'd' x 1 — same shape as the
# existing structural test in zstd_fse_huffman_weight_encode_spec
# (known to encode cleanly through `_zstd_huf_assign_weights`).
# Three distinct code lengths exercise cross-byte packing.
# (The original W13-B 2-symbol probe was blocked by the
# weight balancer rejecting alphabet size 2 — a separate,
# out-of-scope encoder issue.)
val literals: [u8] = [
    0x61u8, 0x62u8, 0x61u8, 0x63u8, 0x61u8, 0x62u8,
    0x61u8, 0x63u8, 0x61u8, 0x62u8, 0x61u8, 0x64u8
]
_round_trip(literals)
```

</details>

#### round-trips a skewed 'a*8 b*4 c*2 d*1' mixed-length input

-  round trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The W13-B probe showed this input decoded as 'a*9 ...'
# because the encoder's byte layout misaligned bit positions
# across byte boundaries. Mixed-length codes (1/2/3 bits)
# exercise the cross-byte packing path.
val literals: [u8] = [
    0x61u8, 0x61u8, 0x61u8, 0x61u8,
    0x61u8, 0x61u8, 0x61u8, 0x61u8,
    0x62u8, 0x62u8, 0x62u8, 0x62u8,
    0x63u8, 0x63u8,
    0x64u8
]
_round_trip(literals)
```

</details>

#### round-trips a highly skewed 'A*16 B*4 C*2 D*1' input

-  round trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Larger run of the most-frequent symbol forces the bit stream
# well past one byte; W13-B saw `byte[16] got=65 want=66`.
val literals: [u8] = [
    0x41u8, 0x41u8, 0x41u8, 0x41u8,
    0x41u8, 0x41u8, 0x41u8, 0x41u8,
    0x41u8, 0x41u8, 0x41u8, 0x41u8,
    0x41u8, 0x41u8, 0x41u8, 0x41u8,
    0x42u8, 0x42u8, 0x42u8, 0x42u8,
    0x43u8, 0x43u8,
    0x44u8
]
_round_trip(literals)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/zstd_huf_round_trip_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- zstd huf encoder round-trips the existing decoder

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
