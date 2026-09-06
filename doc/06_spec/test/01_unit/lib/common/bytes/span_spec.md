# Span Specification

> <details>

<!-- sdn-diagram:id=span_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=span_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

span_spec -> std
span_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=span_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Span Specification

## Scenarios

### ByteSpan

#### reports len and get over the whole slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [10u8, 20u8, 30u8, 40u8]
val s = ByteSpan.new(data)
expect(s.len()).to_equal(4)
expect(s.get(0).to_i64()).to_equal(10)
expect(s.get(3).to_i64()).to_equal(40)
```

</details>

#### fails closed on out-of-bounds get (returns 0, no corruption)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [10u8, 20u8, 30u8]
val s = ByteSpan.new(data)
expect(s.get(3).to_i64()).to_equal(0)
expect(s.get(0 - 1).to_i64()).to_equal(0)
expect(s.get(999).to_i64()).to_equal(0)
```

</details>

#### try_get returns Err out of bounds and Ok in bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [7u8, 8u8]
val s = ByteSpan.new(data)
expect(s.try_get(0).is_ok()).to_equal(true)
expect(s.try_get(2).is_ok()).to_equal(false)
```

</details>

#### slice produces a bounded sub-window

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [1u8, 2u8, 3u8, 4u8, 5u8]
val s = ByteSpan.new(data)
val mid = s.slice(1, 3)
expect(mid.len()).to_equal(3)
expect(mid.get(0).to_i64()).to_equal(2)
expect(mid.get(2).to_i64()).to_equal(4)
```

</details>

#### slice clamps over-long lengths instead of overrunning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [1u8, 2u8, 3u8]
val s = ByteSpan.new(data)
val over = s.slice(1, 100)
expect(over.len()).to_equal(2)
expect(over.get(1).to_i64()).to_equal(3)
```

</details>

#### value equality compares contents not identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: [u8] = [9u8, 8u8, 7u8]
val b: [u8] = [9u8, 8u8, 7u8]
val c: [u8] = [9u8, 8u8, 6u8]
expect(ByteSpan.new(a).equals(ByteSpan.new(b))).to_equal(true)
expect(ByteSpan.new(a).equals(ByteSpan.new(c))).to_equal(false)
```

</details>

#### starts_with detects a prefix span

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [77u8, 90u8, 1u8, 2u8]
val s = ByteSpan.new(data)
val pfx: [u8] = [77u8, 90u8]
expect(s.starts_with(ByteSpan.new(pfx))).to_equal(true)
```

</details>

#### supports == operator for value equality (AC-2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: [u8] = [4u8, 5u8, 6u8]
val b: [u8] = [4u8, 5u8, 6u8]
expect(ByteSpan.new(a) == ByteSpan.new(b)).to_equal(true)
```

</details>

#### iterates: internal sum() and external for-in over to_bytes() (AC-2)

- total = total + byte v to i64
   - Expected: total equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [10u8, 20u8, 30u8]
val s = ByteSpan.new(data)
expect(s.sum()).to_equal(60)
var total = 0
for byte_v in s.to_bytes():
    total = total + byte_v.to_i64()
expect(total).to_equal(60)
```

</details>

### ByteBuffer

#### push_u8 grows length and freeze yields matching ByteSpan

- var b = ByteBuffer new
- b push u8
- b push u8
   - Expected: b.len() equals `2`
   - Expected: span.len() equals `2`
   - Expected: span.get(0).to_i64() equals `100`
   - Expected: span.get(1).to_i64() equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = ByteBuffer.new()
b.push_u8(100u8)
b.push_u8(200u8)
expect(b.len()).to_equal(2)
val span = b.freeze()
expect(span.len()).to_equal(2)
expect(span.get(0).to_i64()).to_equal(100)
expect(span.get(1).to_i64()).to_equal(200)
```

</details>

#### push_span round-trips byte-exactly through freeze (AC-3)

- var b = ByteBuffer new
- b push span
   - Expected: frozen.equals(src_span) is true
   - Expected: frozen.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src: [u8] = [3u8, 1u8, 4u8, 1u8, 5u8, 9u8]
val src_span = ByteSpan.new(src)
var b = ByteBuffer.new()
b.push_span(src_span)
val frozen = b.freeze()
expect(frozen.equals(src_span)).to_equal(true)
expect(frozen.len()).to_equal(6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bytes/span_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ByteSpan
- ByteBuffer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
