# Types Specification

> Tests covering HuffTable canonical codes, HuffTable round-trip, HuffTable from_freqs, negative control, LzToken, SymbolFreqs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Specification

## Scenarios

### HuffTable canonical codes

#### from_code_lengths oracle: sym1 len1 code=0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- from_code_lengths oracle: sym1 len1 code=0


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("from_code_lengths oracle: sym1 len1 code=0")
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cv1 = t.encode_value(1)
val cl1 = t.encode_len(1)
assert_equal(cv1, 0)
assert_equal(cl1, 1)
```

</details>

#### from_code_lengths oracle: sym0 len2 code=2 (0b10)

- from_code_lengths oracle: sym0 len2 code=2 (0b10)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("from_code_lengths oracle: sym0 len2 code=2 (0b10)")
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cv0 = t.encode_value(0)
val cl0 = t.encode_len(0)
assert_equal(cv0, 2)
assert_equal(cl0, 2)
```

</details>

#### from_code_lengths oracle: sym2 len3 code=6 (0b110)

- from_code_lengths oracle: sym2 len3 code=6 (0b110)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("from_code_lengths oracle: sym2 len3 code=6 (0b110)")
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cv2 = t.encode_value(2)
val cl2 = t.encode_len(2)
assert_equal(cv2, 6)
assert_equal(cl2, 3)
```

</details>

#### from_code_lengths oracle: sym3 len3 code=7 (0b111)

- from_code_lengths oracle: sym3 len3 code=7 (0b111)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("from_code_lengths oracle: sym3 len3 code=7 (0b111)")
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cv3 = t.encode_value(3)
val cl3 = t.encode_len(3)
assert_equal(cv3, 7)
assert_equal(cl3, 3)
```

</details>

#### unused symbol (len=0) has code 0 and len 0

- unused symbol (len=0) has code 0 and len 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unused symbol (len=0) has code 0 and len 0")
val lengths: [i64] = [0, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cl0 = t.encode_len(0)
assert_equal(cl0, 0)
```

</details>

#### out-of-range symbol returns len 0

- out-of-range symbol returns len 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("out-of-range symbol returns len 0")
val lengths: [i64] = [2, 1, 3, 3]
val t = HuffTable.from_code_lengths(lengths)
val cl4 = t.encode_len(4)
val clm1 = t.encode_len(-1)
assert_equal(cl4, 0)
assert_equal(clm1, 0)
```

</details>

#### oversubscribed code lengths return empty fail-closed table

- oversubscribed code lengths return empty fail-closed table


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("oversubscribed code lengths return empty fail-closed table")
val lengths: [i64] = [1, 1, 1]
val t = HuffTable.from_code_lengths(lengths)
assert_equal(t.encode_len(0), 0)
assert_equal(t.encode_value(0), 0)
var r = BitReader.msb([0x00u8])
assert_equal(t.decode(r), -1)
```

</details>

#### negative code length returns empty fail-closed table

- negative code length returns empty fail-closed table


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative code length returns empty fail-closed table")
val lengths: [i64] = [1, -1]
val t = HuffTable.from_code_lengths(lengths)
assert_equal(t.encode_len(0), 0)
assert_equal(t.encode_value(0), 0)
var r = BitReader.msb([0x00u8])
assert_equal(t.decode(r), -1)
```

</details>

### HuffTable round-trip

#### encode then decode recovers original sequence

- encode then decode recovers original sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encode then decode recovers original sequence")
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

- decode single symbol sym1 (shortest code 0b0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decode single symbol sym1 (shortest code 0b0)")
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

- decode single symbol sym0 (0b10)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decode single symbol sym0 (0b10)")
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

- most frequent symbol gets shortest code


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("most frequent symbol gets shortest code")
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

- zero-frequency symbols get length 0 (unused)


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-frequency symbols get length 0 (unused)")
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

- 1+1==2 proves runner fires assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("1+1==2 proves runner fires assertions")
assert_equal(1 + 1, 2)
```

</details>

### LzToken

#### Literal carries its byte value

- Literal carries its byte value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Literal carries its byte value")
val t = LzToken.Literal(b: 42)
match t:
    case LzToken.Literal(b: v):
        assert_equal(v, 42)
    case LzToken.Match(distance: d, length: l):
        assert_equal(0, 1)   # wrong branch — fail
```

</details>

#### Match carries distance and length

- Match carries distance and length


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Match carries distance and length")
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

- Literal and Match are distinct cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Literal and Match are distinct cases")
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

- Literal byte value 255


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Literal byte value 255")
val t = LzToken.Literal(b: 255)
match t:
    case LzToken.Literal(b: v):
        assert_equal(v, 255)
    case LzToken.Match(distance: d, length: l):
        assert_equal(0, 1)
```

</details>

#### Match with large distance

- Match with large distance


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Match with large distance")
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

- starts with zero counts and total


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero counts and total")
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

- add increments individual count


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add increments individual count")
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

- add accumulates counts per symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add accumulates counts per symbol")
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

- total tracks all additions


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total tracks all additions")
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

- out-of-range symbols are ignored


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("out-of-range symbols are ignored")
var f = SymbolFreqs.new(4)
f.add(4)     # == max_sym, out of range
f.add(-1)    # negative, out of range
val tot = f.total_count()
assert_equal(tot, 0)
```

</details>

#### hand-computed oracle: 4-symbol alphabet

- hand-computed oracle: 4-symbol alphabet


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hand-computed oracle: 4-symbol alphabet")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HuffTable canonical codes, HuffTable round-trip, HuffTable from_freqs, negative control, LzToken, SymbolFreqs.
- HuffTable canonical codes
- HuffTable round-trip
- HuffTable from_freqs
- negative control
- LzToken
- SymbolFreqs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `387225db74801868fcbf91dcfd8a02ff903ac39992c5f308f06566b44bf2b8d4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `387225db74801868fcbf91dcfd8a02ff903ac39992c5f308f06566b44bf2b8d4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `387225db74801868fcbf91dcfd8a02ff903ac39992c5f308f06566b44bf2b8d4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/typed/types_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/typed/types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/typed/types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/typed/types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/typed/types_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'from_code_lengths oracle: sym1 len1 code=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/typed/types_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'from_code_lengths oracle: sym0 len2 code=2 (0b10)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/typed/types_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'from_code_lengths oracle: sym2 len3 code=6 (0b110)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
