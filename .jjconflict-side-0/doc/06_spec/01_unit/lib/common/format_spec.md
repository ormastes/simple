# Format Specification

> Tests covering format stdlib, str_repeat, format_left, format_right, format_zero_pad, format_hex, format_hex_upper, format_binary, format_signed, format_align.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Format Specification

## Scenarios

### format stdlib

### str_repeat

#### repeats string N times

- repeats string N times
   - Expected: str_repeat("ab", 3) equals `ababab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeats string N times")
expect(str_repeat("ab", 3)).to_equal("ababab")
```

</details>

#### repeat 0 times gives empty

- repeat 0 times gives empty
   - Expected: str_repeat("x", 0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeat 0 times gives empty")
expect(str_repeat("x", 0)).to_equal("")
```

</details>

### format_left

#### pads right with spaces

- pads right with spaces
   - Expected: format_left("hi", 5) equals `hi   `


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads right with spaces")
expect(format_left("hi", 5)).to_equal("hi   ")
```

</details>

#### no padding if already long enough

- no padding if already long enough
   - Expected: format_left("hello", 3) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no padding if already long enough")
expect(format_left("hello", 3)).to_equal("hello")
```

</details>

### format_right

#### pads left with spaces

- pads left with spaces
   - Expected: format_right("hi", 5) equals `   hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads left with spaces")
expect(format_right("hi", 5)).to_equal("   hi")
```

</details>

#### no padding if already long enough

- no padding if already long enough
   - Expected: format_right("hello", 3) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no padding if already long enough")
expect(format_right("hello", 3)).to_equal("hello")
```

</details>

### format_zero_pad

#### pads with zeros

- pads with zeros
   - Expected: format_zero_pad("42", 5) equals `00042`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pads with zeros")
expect(format_zero_pad("42", 5)).to_equal("00042")
```

</details>

#### no padding if long enough

- no padding if long enough
   - Expected: format_zero_pad("12345", 3) equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no padding if long enough")
expect(format_zero_pad("12345", 3)).to_equal("12345")
```

</details>

### format_hex

#### formats zero

- formats zero
   - Expected: format_hex(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats zero")
expect(format_hex(0)).to_equal("0")
```

</details>

#### formats decimal 255

- formats decimal 255
   - Expected: format_hex(255) equals `ff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats decimal 255")
expect(format_hex(255)).to_equal("ff")
```

</details>

#### formats decimal 16

- formats decimal 16
   - Expected: format_hex(16) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats decimal 16")
expect(format_hex(16)).to_equal("10")
```

</details>

#### formats negative input as two's-complement 64-bit hex, never as empty text

- formats negative input as two's-complement 64-bit hex, never as empty text
   - Expected: format_hex(-5) equals `fffffffffffffffb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats negative input as two's-complement 64-bit hex, never as empty text")
# Addresses at or above 0x8000000000000000 are negative i64, so an
# empty result here silently blanked exactly the pointer diagnostics
# that call format_hex. -5 == 0xfffffffffffffffb.
expect(format_hex(-5)).to_equal("fffffffffffffffb")
```

</details>

#### formats -1 as all-ones

- formats -1 as all-ones
   - Expected: format_hex(-1) equals `ffffffffffffffff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats -1 as all-ones")
expect(format_hex(-1)).to_equal("ffffffffffffffff")
```

</details>

#### formats a high address that reads as a negative i64

- formats a high address that reads as a negative i64
   - Expected: format_hex(-9223372036854775808) equals `8000000000000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats a high address that reads as a negative i64")
# 0x8000000000000000 as i64 is the minimum i64 value.
expect(format_hex(-9223372036854775808)).to_equal("8000000000000000")
```

</details>

#### works inside string interpolation — the fix for '0x{v}' printing decimal is '0x{format_hex(v)}', not a {v:x} format-spec (none exists)

- works inside string interpolation — the fix for '0x{v}' printing decimal is '0x{format_hex(v)}', not a {v:x} format-spec (none exists)
   - Expected: "0x{format_hex(offset)}" equals `0xff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works inside string interpolation — the fix for '0x{v}' printing decimal is '0x{format_hex(v)}', not a {v:x} format-spec (none exists)")
val offset = 255
expect("0x{format_hex(offset)}").to_equal("0xff")
```

</details>

#### interpolation with format_hex_upper

- interpolation with format_hex_upper
   - Expected: "0x{format_hex_upper(offset)}" equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolation with format_hex_upper")
val offset = 255
expect("0x{format_hex_upper(offset)}").to_equal("0xFF")
```

</details>

### format_hex_upper

#### formats uppercase hex

- formats uppercase hex
   - Expected: format_hex_upper(255) equals `FF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats uppercase hex")
expect(format_hex_upper(255)).to_equal("FF")
```

</details>

#### formats negative input as uppercase two's-complement hex

- formats negative input as uppercase two's-complement hex
   - Expected: format_hex_upper(-1) equals `FFFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats negative input as uppercase two's-complement hex")
expect(format_hex_upper(-1)).to_equal("FFFFFFFFFFFFFFFF")
```

</details>

### format_binary

#### formats zero

- formats zero
   - Expected: format_binary(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats zero")
expect(format_binary(0)).to_equal("0")
```

</details>

#### formats 8 as binary

- formats 8 as binary
   - Expected: format_binary(8) equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats 8 as binary")
expect(format_binary(8)).to_equal("1000")
```

</details>

#### formats 255 as binary

- formats 255 as binary
   - Expected: format_binary(255) equals `11111111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats 255 as binary")
expect(format_binary(255)).to_equal("11111111")
```

</details>

### format_signed

#### positive with plus sign

- positive with plus sign
   - Expected: format_signed(42) equals `+42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive with plus sign")
expect(format_signed(42)).to_equal("+42")
```

</details>

#### negative keeps minus

- negative keeps minus
   - Expected: format_signed(-5) equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative keeps minus")
expect(format_signed(-5)).to_equal("-5")
```

</details>

### format_align

#### left align

- left align
   - Expected: format_align("x", 3, "left") equals `x  `


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("left align")
expect(format_align("x", 3, "left")).to_equal("x  ")
```

</details>

#### right align

- right align
   - Expected: format_align("x", 3, "right") equals `  x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("right align")
expect(format_align("x", 3, "right")).to_equal("  x")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/format_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering format stdlib, str_repeat, format_left, format_right, format_zero_pad, format_hex, format_hex_upper, format_binary, format_signed, format_align.
- format stdlib
- str_repeat
- format_left
- format_right
- format_zero_pad
- format_hex
- format_hex_upper
- format_binary
- format_signed
- format_align

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

- Canonical SPipe generation for source `75475af3c57d3f88cf8611abe63d3d7f19ce7f493e0aecf187a0af0c71506e95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75475af3c57d3f88cf8611abe63d3d7f19ce7f493e0aecf187a0af0c71506e95`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75475af3c57d3f88cf8611abe63d3d7f19ce7f493e0aecf187a0af0c71506e95`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/format_spec.spl
mirror: doc/06_spec/01_unit/lib/common/format_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/format_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/format_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/format_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'repeats string N times' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/format_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'repeat 0 times gives empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/format_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pads right with spaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
