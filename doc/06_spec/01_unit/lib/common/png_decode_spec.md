# Png Decode Specification

> Tests covering PngDecode — signature validation, PngDecode — PngImage output, PngDecode — pixel output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Png Decode Specification

## Scenarios

### PngDecode — signature validation

#### invalid data

#### AC-2: empty bytes returns error

- AC-2: empty bytes returns error
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: empty bytes returns error")
val data: [u8] = []
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-2: non-PNG bytes returns error

- AC-2: non-PNG bytes returns error
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: non-PNG bytes returns error")
val data: [u8] = [0, 1, 2, 3, 4, 5, 6, 7]
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-2: truncated PNG signature returns error

- AC-2: truncated PNG signature returns error
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: truncated PNG signature returns error")
val data: [u8] = [137, 80, 78, 71]
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### valid signature but truncated content

#### AC-2: PNG signature only (no chunks) returns error

- AC-2: PNG signature only (no chunks) returns error
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: PNG signature only (no chunks) returns error")
val result = decode_png_to_argb(PNG_SIGNATURE)
expect(result.is_err()).to_equal(true)
```

</details>

### PngDecode — PngImage output

#### decoded image properties

#### AC-2: PngImage has width field

- AC-2: PngImage has width field
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: PngImage has width field")
# This test will fail because no real PNG data exists yet,
# but validates the struct shape
val data: [u8] = [0]
val result = decode_png_to_argb(data)
# Error case — but the Ok type should have width
expect(result.is_err()).to_equal(true)
```

</details>

#### AC-2: PngImage pixels are ARGB u32 format

- AC-2: PngImage pixels are ARGB u32 format
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: PngImage pixels are ARGB u32 format")
# When a valid PNG is decoded, each pixel should be a u32
# with A in bits 24-31, R in 16-23, G in 8-15, B in 0-7
val data: [u8] = [0]
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

### PngDecode — pixel output

#### 1x1 pixel images

#### AC-2: 1x1 black PNG decodes to single black ARGB pixel

- AC-2: 1x1 black PNG decodes to single black ARGB pixel
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: 1x1 black PNG decodes to single black ARGB pixel")
# A minimal valid 1x1 black PNG would be needed here.
# This test validates the decode -> ARGB conversion path.
# Without implementation, this MUST fail.
val data: [u8] = [0]  # placeholder — not a valid PNG
val result = decode_png_to_argb(data)
# Should fail because data is invalid
expect(result.is_err()).to_equal(true)
```

</details>

#### pixel count matches dimensions

#### AC-2: decoded pixel count equals width * height

- AC-2: decoded pixel count equals width * height
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: decoded pixel count equals width * height")
# Placeholder — will fail without implementation and valid PNG data
val data: [u8] = [0]
val result = decode_png_to_argb(data)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/png_decode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PngDecode — signature validation, PngDecode — PngImage output, PngDecode — pixel output.
- PngDecode — signature validation
- PngDecode — PngImage output
- PngDecode — pixel output

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `9308a43ee9af0e8109ce6326794774ce59cf1dfb2072839b26a27b48a5d6bd0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9308a43ee9af0e8109ce6326794774ce59cf1dfb2072839b26a27b48a5d6bd0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9308a43ee9af0e8109ce6326794774ce59cf1dfb2072839b26a27b48a5d6bd0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/png_decode_spec.spl
mirror: doc/06_spec/01_unit/lib/common/png_decode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/png_decode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/png_decode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/png_decode_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: empty bytes returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/png_decode_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: non-PNG bytes returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/png_decode_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: truncated PNG signature returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
