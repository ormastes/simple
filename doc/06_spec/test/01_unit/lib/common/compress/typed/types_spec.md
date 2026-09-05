# Types Specification

> <details>

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec -> std
types_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Specification

## Scenarios

### HuffTable canonical codes

#### from_code_lengths oracle: sym1 len1 code=0

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cv1 = t.encode_value(1)
val cl1 = t.encode_len(1)
assert_equal(cv1, 0)
assert_equal(cl1, 1)
```

</details>

#### from_code_lengths oracle: sym0 len2 code=2 (0b10)

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cv0 = t.encode_value(0)
val cl0 = t.encode_len(0)
assert_equal(cv0, 2)
assert_equal(cl0, 2)
```

</details>

#### from_code_lengths oracle: sym2 len3 code=6 (0b110)

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cv2 = t.encode_value(2)
val cl2 = t.encode_len(2)
assert_equal(cv2, 6)
assert_equal(cl2, 3)
```

</details>

#### from_code_lengths oracle: sym3 len3 code=7 (0b111)

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cv3 = t.encode_value(3)
val cl3 = t.encode_len(3)
assert_equal(cv3, 7)
assert_equal(cl3, 3)
```

</details>

#### unused symbol (len=0) has code 0 and len 0

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths: [i64] = [0, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cl0 = t.encode_len(0)
assert_equal(cl0, 0)
```

</details>

#### out-of-range symbol returns len 0

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cl4 = t.encode_len(4)
val clm1 = t.encode_len(-1)
assert_equal(cl4, 0)
assert_equal(clm1, 0)
```

</details>

### HuffTable round-trip

#### encode then decode recovers original sequence

- var ht = HuffTable from code lengths
- var w = BitWriter msb
- ht encode
- w align
- var r = BitReader msb
- decoded push
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths: [i64] = [2, 1, 3, 3]
var ht = HuffTable.from_code_lengths(lengths)

# Encode sequence
val seq: [i64] = [0, 1, 2, 3, 1, 0]
var w = BitWriter.msb()
var ei = 0
while ei < seq.len():
    ht.encode(seq[ei], w)
    ei = ei + 1
w.align()
val buf = w.finish()
val sp = buf.freeze()
val data = sp.to_bytes()

# Decode — separate code path (decode walks bit-by-bit via canonical ranges)
var r = BitReader.msb(data)
var decoded: [i64] = []
var di = 0
while di < 6:
    val s = ht.decode(r)
    decoded.push(s)
    di = di + 1

# Verify each position against absolute oracle values
val d0 = decoded[0]
val d1 = decoded[1]
val d2 = decoded[2]
val d3 = decoded[3]
val d4 = decoded[4]
val d5 = decoded[5]
assert_equal(d0, 0)
assert_equal(d1, 1)
assert_equal(d2, 2)
assert_equal(d3, 3)
assert_equal(d4, 1)
assert_equal(d5, 0)
```

</details>

#### decode single symbol sym1 (shortest code 0b0)

- var ht = HuffTable from code lengths
- var w = BitWriter msb
- ht encode
- w align
- var r = BitReader msb
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths: [i64] = [2, 1, 3, 3]
var ht = HuffTable.from_code_lengths(lengths)
var w = BitWriter.msb()
ht.encode(1, w)
w.align()
val buf = w.finish()
val sp = buf.freeze()
val data = sp.to_bytes()
var r = BitReader.msb(data)
val s = ht.decode(r)
assert_equal(s, 1)
```

</details>

#### decode single symbol sym0 (0b10)

- var ht = HuffTable from code lengths
- var w = BitWriter msb
- ht encode
- w align
- var r = BitReader msb
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lengths: [i64] = [2, 1, 3, 3]
var ht = HuffTable.from_code_lengths(lengths)
var w = BitWriter.msb()
ht.encode(0, w)
w.align()
val buf = w.finish()
val sp = buf.freeze()
val data = sp.to_bytes()
var r = BitReader.msb(data)
val s = ht.decode(r)
assert_equal(s, 0)
```

</details>

### HuffTable from_freqs

#### most frequent symbol gets shortest code

- var f = SymbolFreqs new
- f add
- f add
- f add
- f add
- f add
- f add
- f add
- f add
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SymbolFreqs.new(4)
# sym2 is most frequent (5 times)
f.add(2)
f.add(2)
f.add(2)
f.add(2)
f.add(2)
f.add(0)
f.add(1)
f.add(3)
val t = HuffTable.from_freqs(f, 8)
val l2 = t.encode_len(2)
val l0 = t.encode_len(0)
val l1 = t.encode_len(1)
val l3 = t.encode_len(3)
val l2_le_l0 = l2 <= l0
val l2_le_l1 = l2 <= l1
val l2_le_l3 = l2 <= l3
assert_true(l2_le_l0)
assert_true(l2_le_l1)
assert_true(l2_le_l3)
```

</details>

#### zero-frequency symbols get length 0 (unused)

- var f = SymbolFreqs new
- f add
- f add
- assert equal
- assert equal
- assert equal
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SymbolFreqs.new(4)
f.add(1)
f.add(1)
val t = HuffTable.from_freqs(f, 8)
val el0 = t.encode_len(0)
val el2 = t.encode_len(2)
val el3 = t.encode_len(3)
val el1 = t.encode_len(1)
assert_equal(el0, 0)
assert_equal(el2, 0)
assert_equal(el3, 0)
val el1_pos = el1 > 0
assert_true(el1_pos)
```

</details>

### negative control

#### 1+1==2 proves runner fires assertions

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(1 + 1, 2)
```

</details>

### LzToken

#### Literal carries its byte value

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = LzToken.Literal(b: 42)
match t:
    case LzToken.Literal(b: v):
        assert_equal(v, 42)
    case LzToken.Match(distance: d, length: l):
        assert_equal(0, 1)   # wrong branch — fail
```

</details>

#### Match carries distance and length

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = LzToken.Match(distance: 8, length: 3)
match t:
    case LzToken.Literal(b: v):
        assert_equal(0, 1)   # wrong branch — fail
    case LzToken.Match(distance: d, length: l):
        assert_equal(d, 8)
        assert_equal(l, 3)
```

</details>

#### Literal and Match are distinct cases

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lit = LzToken.Literal(b: 0)
val mat = LzToken.Match(distance: 1, length: 1)
var lit_count = 0
var match_count = 0
match lit:
    case LzToken.Literal(b: v):
        lit_count = lit_count + 1
    case LzToken.Match(distance: d, length: l):
        match_count = match_count + 1
match mat:
    case LzToken.Literal(b: v):
        lit_count = lit_count + 1
    case LzToken.Match(distance: d, length: l):
        match_count = match_count + 1
assert_equal(lit_count, 1)
assert_equal(match_count, 1)
```

</details>

#### Literal byte value 255

- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = LzToken.Literal(b: 255)
match t:
    case LzToken.Literal(b: v):
        assert_equal(v, 255)
    case LzToken.Match(distance: d, length: l):
        assert_equal(0, 1)
```

</details>

#### Match with large distance

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = LzToken.Match(distance: 32768, length: 258)
match t:
    case LzToken.Literal(b: v):
        assert_equal(0, 1)
    case LzToken.Match(distance: d, length: l):
        assert_equal(d, 32768)
        assert_equal(l, 258)
```

</details>

### SymbolFreqs

#### starts with zero counts and total

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = SymbolFreqs.new(286)
val c0 = f.count(0)
val c65 = f.count(65)
val tot = f.total_count()
assert_equal(c0, 0)
assert_equal(c65, 0)
assert_equal(tot, 0)
```

</details>

#### add increments individual count

- var f = SymbolFreqs new
- f add
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SymbolFreqs.new(10)
f.add(3)
val c3 = f.count(3)
val c2 = f.count(2)
val c4 = f.count(4)
assert_equal(c3, 1)
assert_equal(c2, 0)
assert_equal(c4, 0)
```

</details>

#### add accumulates counts per symbol

- var f = SymbolFreqs new
- f add
- f add
- f add
- f add
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SymbolFreqs.new(10)
f.add(5)
f.add(5)
f.add(5)
f.add(2)
val c5 = f.count(5)
val c2 = f.count(2)
assert_equal(c5, 3)
assert_equal(c2, 1)
```

</details>

#### total tracks all additions

- var f = SymbolFreqs new
- f add
- f add
- f add
- f add
- f add
- f add
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SymbolFreqs.new(10)
f.add(0)
f.add(1)
f.add(1)
f.add(2)
f.add(2)
f.add(2)
val tot = f.total_count()
assert_equal(tot, 6)
```

</details>

#### out-of-range symbols are ignored

- var f = SymbolFreqs new
- f add
- f add
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SymbolFreqs.new(4)
f.add(4)     # == max_sym, out of range
f.add(-1)    # negative, out of range
val tot = f.total_count()
assert_equal(tot, 0)
```

</details>

#### hand-computed oracle: 4-symbol alphabet

- var f = SymbolFreqs new
- f add
- f add
- f add
- f add
- f add
- f add
- f add
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f = SymbolFreqs.new(4)
f.add(0)
f.add(1)
f.add(1)
f.add(2)
f.add(2)
f.add(2)
f.add(3)
val c0 = f.count(0)
val c1 = f.count(1)
val c2 = f.count(2)
val c3 = f.count(3)
val tot = f.total_count()
assert_equal(c0, 1)
assert_equal(c1, 2)
assert_equal(c2, 3)
assert_equal(c3, 1)
assert_equal(tot, 7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/typed/types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HuffTable canonical codes
- HuffTable round-trip
- HuffTable from_freqs
- negative control
- LzToken
- SymbolFreqs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
