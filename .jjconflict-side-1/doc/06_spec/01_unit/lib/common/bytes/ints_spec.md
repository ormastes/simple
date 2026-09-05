# Ints Specification

> Tests covering Little-endian views, Big-endian views.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ints Specification

## Scenarios

### Little-endian views

#### U16le decodes [0x34,0x12] = 0x1234

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- U16le decodes [0x34,0x12] = 0x1234
   - Expected: U16le.load(ByteSpan.new(data), 0).value() equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U16le decodes [0x34,0x12] = 0x1234")
val data: [u8] = [0x34u8, 0x12u8]
expect(U16le.load(ByteSpan.new(data), 0).value()).to_equal(0x1234)
```

</details>

#### U32le decodes [0x78,0x56,0x34,0x12] = 0x12345678

- U32le decodes [0x78,0x56,0x34,0x12] = 0x12345678
   - Expected: U32le.load(ByteSpan.new(data), 0).value() equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U32le decodes [0x78,0x56,0x34,0x12] = 0x12345678")
val data: [u8] = [0x78u8, 0x56u8, 0x34u8, 0x12u8]
expect(U32le.load(ByteSpan.new(data), 0).value()).to_equal(0x12345678)
```

</details>

#### U16le stores 0xBEEF as [0xEF,0xBE]

- U16le stores 0xBEEF as [0xEF,0xBE]
   - Expected: s.get(0).to_i64() equals `0xEF`
   - Expected: s.get(1).to_i64() equals `0xBE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U16le stores 0xBEEF as [0xEF,0xBE]")
var b = ByteBuffer.new()
U16le.of(0xBEEF).store(b)
val s = b.freeze()
expect(s.get(0).to_i64()).to_equal(0xEF)
expect(s.get(1).to_i64()).to_equal(0xBE)
```

</details>

#### U32le round-trips 0xDEADBEEF

- U32le round-trips 0xDEADBEEF
   - Expected: U32le.load(sp, 0).value() equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U32le round-trips 0xDEADBEEF")
val sp = U32le.of(0xDEADBEEF).to_span()
expect(U32le.load(sp, 0).value()).to_equal(0xDEADBEEF)
```

</details>

#### U64le round-trips 0x0102030405060708

- U64le round-trips 0x0102030405060708
   - Expected: sp.get(0).to_i64() equals `0x08`
   - Expected: sp.get(7).to_i64() equals `0x01`
   - Expected: U64le.load(sp, 0).value() equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U64le round-trips 0x0102030405060708")
val v = 0x0102030405060708
val sp = U64le.of(v).to_span()
expect(sp.get(0).to_i64()).to_equal(0x08)
expect(sp.get(7).to_i64()).to_equal(0x01)
expect(U64le.load(sp, 0).value()).to_equal(v)
```

</details>

### Big-endian views

#### U16be decodes [0x12,0x34] = 0x1234

- U16be decodes [0x12,0x34] = 0x1234
   - Expected: U16be.load(ByteSpan.new(data), 0).value() equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U16be decodes [0x12,0x34] = 0x1234")
val data: [u8] = [0x12u8, 0x34u8]
expect(U16be.load(ByteSpan.new(data), 0).value()).to_equal(0x1234)
```

</details>

#### U32be decodes [0x12,0x34,0x56,0x78] = 0x12345678

- U32be decodes [0x12,0x34,0x56,0x78] = 0x12345678
   - Expected: U32be.load(ByteSpan.new(data), 0).value() equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U32be decodes [0x12,0x34,0x56,0x78] = 0x12345678")
val data: [u8] = [0x12u8, 0x34u8, 0x56u8, 0x78u8]
expect(U32be.load(ByteSpan.new(data), 0).value()).to_equal(0x12345678)
```

</details>

#### U16be stores 0xBEEF as [0xBE,0xEF]

- U16be stores 0xBEEF as [0xBE,0xEF]
   - Expected: s.get(0).to_i64() equals `0xBE`
   - Expected: s.get(1).to_i64() equals `0xEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U16be stores 0xBEEF as [0xBE,0xEF]")
var b = ByteBuffer.new()
U16be.of(0xBEEF).store(b)
val s = b.freeze()
expect(s.get(0).to_i64()).to_equal(0xBE)
expect(s.get(1).to_i64()).to_equal(0xEF)
```

</details>

#### U32be round-trips 0xCAFEBABE

- U32be round-trips 0xCAFEBABE
   - Expected: sp.get(0).to_i64() equals `0xCA`
   - Expected: sp.get(3).to_i64() equals `0xBE`
   - Expected: U32be.load(sp, 0).value() equals `0xCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U32be round-trips 0xCAFEBABE")
val sp = U32be.of(0xCAFEBABE).to_span()
expect(sp.get(0).to_i64()).to_equal(0xCA)
expect(sp.get(3).to_i64()).to_equal(0xBE)
expect(U32be.load(sp, 0).value()).to_equal(0xCAFEBABE)
```

</details>

#### U64be round-trips 0x0102030405060708 (MSB first)

- U64be round-trips 0x0102030405060708 (MSB first)
   - Expected: sp.get(0).to_i64() equals `0x01`
   - Expected: sp.get(7).to_i64() equals `0x08`
   - Expected: U64be.load(sp, 0).value() equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("U64be round-trips 0x0102030405060708 (MSB first)")
val v = 0x0102030405060708
val sp = U64be.of(v).to_span()
expect(sp.get(0).to_i64()).to_equal(0x01)
expect(sp.get(7).to_i64()).to_equal(0x08)
expect(U64be.load(sp, 0).value()).to_equal(v)
```

</details>

#### LE and BE of the same value produce reversed byte order

- LE and BE of the same value produce reversed byte order
   - Expected: le.get(0).to_i64() equals `be.get(3).to_i64()`
   - Expected: le.get(3).to_i64() equals `be.get(0).to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LE and BE of the same value produce reversed byte order")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Little-endian views, Big-endian views.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc4836cfd63ee9a5933c034146bbd92e60df3ffe4b9ede422fd1410e76453490`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc4836cfd63ee9a5933c034146bbd92e60df3ffe4b9ede422fd1410e76453490`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc4836cfd63ee9a5933c034146bbd92e60df3ffe4b9ede422fd1410e76453490`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/bytes/ints_spec.spl
mirror: doc/06_spec/01_unit/lib/common/bytes/ints_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/bytes/ints_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/bytes/ints_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/bytes/ints_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'U16le decodes [0x34,0x12] = 0x1234' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/bytes/ints_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'U32le decodes [0x78,0x56,0x34,0x12] = 0x12345678' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/bytes/ints_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'U16le stores 0xBEEF as [0xEF,0xBE]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
