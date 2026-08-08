# Window Specification

> <details>

<!-- sdn-diagram:id=window_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_spec -> std
window_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Specification

## Scenarios

### RingWindow

#### at_distance recovers recently pushed bytes (d=1 is most recent)

- var w = RingWindow new
- w push
- w push
- w push
   - Expected: w.at_distance(1).to_i64() equals `33`
   - Expected: w.at_distance(2).to_i64() equals `22`
   - Expected: w.at_distance(3).to_i64() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = RingWindow.new(8)
w.push(11u8)
w.push(22u8)
w.push(33u8)
expect(w.at_distance(1).to_i64()).to_equal(33)
expect(w.at_distance(2).to_i64()).to_equal(22)
expect(w.at_distance(3).to_i64()).to_equal(11)
```

</details>

#### fails closed on distance beyond filled size

- var w = RingWindow new
- w push
   - Expected: w.at_distance(2).to_i64() equals `0`
   - Expected: w.at_distance(0).to_i64() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = RingWindow.new(8)
w.push(5u8)
expect(w.at_distance(2).to_i64()).to_equal(0)
expect(w.at_distance(0).to_i64()).to_equal(0)
```

</details>

#### evicts oldest beyond capacity (wraparound invariant)

- var w = RingWindow new
- w push
- w push
- w push
- w push
   - Expected: w.size() equals `3`
   - Expected: w.at_distance(1).to_i64() equals `4`
   - Expected: w.at_distance(3).to_i64() equals `2`
   - Expected: w.at_distance(4).to_i64() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = RingWindow.new(3)
w.push(1u8)
w.push(2u8)
w.push(3u8)
w.push(4u8)
expect(w.size()).to_equal(3)
expect(w.at_distance(1).to_i64()).to_equal(4)
expect(w.at_distance(3).to_i64()).to_equal(2)
expect(w.at_distance(4).to_i64()).to_equal(0)
```

</details>

#### match_len finds the longest match against a span

- var w = RingWindow new
- w push
- w push
- w push
   - Expected: w.match_len(ByteSpan.new(probe), 0) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = RingWindow.new(16)
w.push(65u8)
w.push(66u8)
w.push(67u8)
# history (most recent first) is C,B,A. A span A,B,C matches all 3.
val probe: [u8] = [65u8, 66u8, 67u8]
expect(w.match_len(ByteSpan.new(probe), 0)).to_equal(3)
```

</details>

#### copy_match performs an overlapping LZ77 run-length copy

- var w = RingWindow new
- w push
- w copy match
   - Expected: w.size() equals `5`
   - Expected: w.at_distance(1).to_i64() equals `97`
   - Expected: w.at_distance(5).to_i64() equals `97`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = RingWindow.new(16)
w.push(97u8)            # 'a'
# distance 1, length 4 -> repeat 'a' four times
w.copy_match(1, 4)
expect(w.size()).to_equal(5)
expect(w.at_distance(1).to_i64()).to_equal(97)
expect(w.at_distance(5).to_i64()).to_equal(97)
```

</details>

#### copy_match with distance 2 repeats a two-byte pattern

- var w = RingWindow new
- w push
- w push
- w copy match
   - Expected: w.at_distance(4).to_i64() equals `1`
   - Expected: w.at_distance(3).to_i64() equals `2`
   - Expected: w.at_distance(2).to_i64() equals `1`
   - Expected: w.at_distance(1).to_i64() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = RingWindow.new(16)
w.push(1u8)
w.push(2u8)
w.copy_match(2, 4)      # repeats 1,2,1,2
expect(w.at_distance(4).to_i64()).to_equal(1)
expect(w.at_distance(3).to_i64()).to_equal(2)
expect(w.at_distance(2).to_i64()).to_equal(1)
expect(w.at_distance(1).to_i64()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bytes/window_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RingWindow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
