# Ints Specification

> <details>

<!-- sdn-diagram:id=ints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ints_spec -> std
ints_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ints Specification

## Scenarios

### Little-endian views

#### U16le decodes [0x34,0x12] = 0x1234

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x34u8, 0x12u8]
expect(U16le.load(ByteSpan.new(data), 0).value()).to_equal(0x1234)
```

</details>

#### U32le decodes [0x78,0x56,0x34,0x12] = 0x12345678

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x78u8, 0x56u8, 0x34u8, 0x12u8]
expect(U32le.load(ByteSpan.new(data), 0).value()).to_equal(0x12345678)
```

</details>

#### U16le stores 0xBEEF as [0xEF,0xBE]

- var b = ByteBuffer new
- U16le of
   - Expected: s.get(0).to_i64() equals `0xEF`
   - Expected: s.get(1).to_i64() equals `0xBE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = ByteBuffer.new()
U16le.of(0xBEEF).store(b)
val s = b.freeze()
expect(s.get(0).to_i64()).to_equal(0xEF)
expect(s.get(1).to_i64()).to_equal(0xBE)
```

</details>

#### U32le round-trips 0xDEADBEEF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = U32le.of(0xDEADBEEF).to_span()
expect(U32le.load(sp, 0).value()).to_equal(0xDEADBEEF)
```

</details>

#### U64le round-trips 0x0102030405060708

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = 0x0102030405060708
val sp = U64le.of(v).to_span()
expect(sp.get(0).to_i64()).to_equal(0x08)
expect(sp.get(7).to_i64()).to_equal(0x01)
expect(U64le.load(sp, 0).value()).to_equal(v)
```

</details>

### Big-endian views

#### U16be decodes [0x12,0x34] = 0x1234

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x12u8, 0x34u8]
expect(U16be.load(ByteSpan.new(data), 0).value()).to_equal(0x1234)
```

</details>

#### U32be decodes [0x12,0x34,0x56,0x78] = 0x12345678

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [0x12u8, 0x34u8, 0x56u8, 0x78u8]
expect(U32be.load(ByteSpan.new(data), 0).value()).to_equal(0x12345678)
```

</details>

#### U16be stores 0xBEEF as [0xBE,0xEF]

- var b = ByteBuffer new
- U16be of
   - Expected: s.get(0).to_i64() equals `0xBE`
   - Expected: s.get(1).to_i64() equals `0xEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = ByteBuffer.new()
U16be.of(0xBEEF).store(b)
val s = b.freeze()
expect(s.get(0).to_i64()).to_equal(0xBE)
expect(s.get(1).to_i64()).to_equal(0xEF)
```

</details>

#### U32be round-trips 0xCAFEBABE

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = U32be.of(0xCAFEBABE).to_span()
expect(sp.get(0).to_i64()).to_equal(0xCA)
expect(sp.get(3).to_i64()).to_equal(0xBE)
expect(U32be.load(sp, 0).value()).to_equal(0xCAFEBABE)
```

</details>

#### U64be round-trips 0x0102030405060708 (MSB first)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = 0x0102030405060708
val sp = U64be.of(v).to_span()
expect(sp.get(0).to_i64()).to_equal(0x01)
expect(sp.get(7).to_i64()).to_equal(0x08)
expect(U64be.load(sp, 0).value()).to_equal(v)
```

</details>

#### LE and BE of the same value produce reversed byte order

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val le = U32le.of(0x11223344).to_span()
val be = U32be.of(0x11223344).to_span()
expect(le.get(0).to_i64()).to_equal(be.get(3).to_i64())
expect(le.get(3).to_i64()).to_equal(be.get(0).to_i64())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bytes/ints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Little-endian views
- Big-endian views

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
