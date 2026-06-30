# Adler32 Specification

> <details>

<!-- sdn-diagram:id=adler32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adler32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adler32_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adler32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adler32 Specification

## Scenarios

### adler32 — RFC 1950

#### empty input returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
expect(adler32(data)).to_equal(1)
```

</details>

#### single byte 'a' (97) returns 0x00620062

- var data: [u8] =  ascii bytes
   - Expected: adler32(data) equals `6422626`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A = 1+97 = 98 = 0x62, B = 0+98 = 98 = 0x62
# Result = (98 << 16) | 98 = 6422626
var data: [u8] = _ascii_bytes("a")
expect(adler32(data)).to_equal(6422626)
```

</details>

#### 'abc' returns 0x024D0127

- var data: [u8] =  ascii bytes
   - Expected: adler32(data) equals `38600999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After 'a'(97): A=98, B=98
# After 'b'(98): A=196, B=294
# After 'c'(99): A=295, B=589
# Result = (589 << 16) | 295 = 38600999
var data: [u8] = _ascii_bytes("abc")
expect(adler32(data)).to_equal(38600999)
```

</details>

#### 'Wikipedia' returns 0x11E60398

- var data: [u8] =  ascii bytes
   - Expected: adler32(data) equals `300286872`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Well-known reference vector
# Result = (4582 << 16) | 920 = 300286872
var data: [u8] = _ascii_bytes("Wikipedia")
expect(adler32(data)).to_equal(300286872)
```

</details>

#### all-zero bytes of length 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A = 1+0+0+0+0 = 1, B = 1+1+1+1 = 4
# Result = (4 << 16) | 1 = 262145
var data: [u8] = [0, 0, 0, 0]
expect(adler32(data)).to_equal(262145)
```

</details>

#### single byte 0xFF (255)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A = 1+255 = 256, B = 0+256 = 256
# Result = (256 << 16) | 256 = 16777472
var data: [u8] = [255]
expect(adler32(data)).to_equal(16777472)
```

</details>

### fletcher32 — 16-bit LE words

#### empty input returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
expect(fletcher32(data)).to_equal(0)
```

</details>

#### 'abcd' (two 16-bit words) returns correct checksum

- var data: [u8] =  ascii bytes
   - Expected: fletcher32(data) equals `690407108`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word1 = 97|(98<<8) = 25185, word2 = 99|(100<<8) = 25699
# sum1: 0 -> 25185 -> 50884
# sum2: 0 -> 25185 -> (25185+50884)%65535 = 10534+2048... = 10536
# Result = (10536 << 16) | 50884 = 690407108
var data: [u8] = _ascii_bytes("abcd")
expect(fletcher32(data)).to_equal(690407108)
```

</details>

#### 'abcde' (odd length, zero-padded) returns correct checksum

- var data: [u8] =  ascii bytes
   - Expected: fletcher32(data) equals `4031760169`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word1 = 97|(98<<8)=25185, word2 = 99|(100<<8)=25699, word3 = 101|(0<<8)=101
# sum1: 0 -> 25185 -> 50884 -> 50985
# sum2: 0 -> 25185 -> 10536 -> 61521
# Result = (61521 << 16) | 50985 = 4031760169
var data: [u8] = _ascii_bytes("abcde")
expect(fletcher32(data)).to_equal(4031760169)
```

</details>

#### single byte pads with zero high byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 42|(0<<8) = 42
# sum1 = 42, sum2 = 42
# Result = (42 << 16) | 42 = 2752554
var data: [u8] = [42]
expect(fletcher32(data)).to_equal(2752554)
```

</details>

#### two zero bytes returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# word = 0|(0<<8) = 0
# sum1 = 0, sum2 = 0
# Result = 0
var data: [u8] = [0, 0]
expect(fletcher32(data)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hash/adler32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- adler32 — RFC 1950
- fletcher32 — 16-bit LE words

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
