# Png Encode Specification

> Tests covering png_encode encode_argb_to_png, png_encode encode_argb_to_png_rgb.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Png Encode Specification

## Scenarios

### png_encode encode_argb_to_png

#### 2x2 RGBA round-trip

#### decodes back to the exact source pixels via decode_png_to_argb

- decodes back to the exact source pixels via decode_png_to_argb
   - Expected: result.is_err() is false
   - Expected: img.width equals `2`
   - Expected: img.height equals `2`
   - Expected: img.pixels equals `PIXELS_2X2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes back to the exact source pixels via decode_png_to_argb")
val bytes = encode_argb_to_png(PIXELS_2X2, 2, 2)
val result = decode_png_to_argb(bytes)
expect(result.is_err()).to_equal(false)
val img = result.unwrap()
expect(img.width).to_equal(2)
expect(img.height).to_equal(2)
expect(img.pixels).to_equal(PIXELS_2X2)
```

</details>

#### exact magic and IHDR bytes

#### starts with the 8-byte PNG signature

- starts with the 8-byte PNG signature
   - Expected: sig equals `PNG_SIGNATURE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts with the 8-byte PNG signature")
val bytes = encode_argb_to_png(PIXELS_2X2, 2, 2)
var sig: [u8] = []
var i = 0
while i < 8:
    sig.push(bytes[i])
    i = i + 1
expect(sig).to_equal(PNG_SIGNATURE)
```

</details>

#### emits an IHDR chunk with exact length, type, width/height, bit depth 8, color type 6

- emits an IHDR chunk with exact length, type, width/height, bit depth 8, color type 6
   - Expected: bytes[8] equals `0u8`
   - Expected: bytes[9] equals `0u8`
   - Expected: bytes[10] equals `0u8`
   - Expected: bytes[11] equals `13u8`
   - Expected: chunk_type equals `IHDR_TYPE`
   - Expected: bytes[16] equals `0u8`
   - Expected: bytes[17] equals `0u8`
   - Expected: bytes[18] equals `0u8`
   - Expected: bytes[19] equals `2u8`
   - Expected: bytes[20] equals `0u8`
   - Expected: bytes[21] equals `0u8`
   - Expected: bytes[22] equals `0u8`
   - Expected: bytes[23] equals `2u8`
   - Expected: bytes[24] equals `8u8`
   - Expected: bytes[25] equals `6u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits an IHDR chunk with exact length, type, width/height, bit depth 8, color type 6")
val bytes = encode_argb_to_png(PIXELS_2X2, 2, 2)
# chunk length (offset 8..12, big-endian) == 13
expect(bytes[8]).to_equal(0u8)
expect(bytes[9]).to_equal(0u8)
expect(bytes[10]).to_equal(0u8)
expect(bytes[11]).to_equal(13u8)
# chunk type (offset 12..16) == "IHDR"
var chunk_type: [u8] = []
var j = 12
while j < 16:
    chunk_type.push(bytes[j])
    j = j + 1
expect(chunk_type).to_equal(IHDR_TYPE)
# width big-endian == 2 (offset 16..20)
expect(bytes[16]).to_equal(0u8)
expect(bytes[17]).to_equal(0u8)
expect(bytes[18]).to_equal(0u8)
expect(bytes[19]).to_equal(2u8)
# height big-endian == 2 (offset 20..24)
expect(bytes[20]).to_equal(0u8)
expect(bytes[21]).to_equal(0u8)
expect(bytes[22]).to_equal(0u8)
expect(bytes[23]).to_equal(2u8)
# bit depth 8, color type 6 (RGBA)
expect(bytes[24]).to_equal(8u8)
expect(bytes[25]).to_equal(6u8)
```

</details>

#### determinism

#### produces byte-identical output across two separate encode calls

- produces byte-identical output across two separate encode calls
   - Expected: bytes1 equals `bytes2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces byte-identical output across two separate encode calls")
val bytes1 = encode_argb_to_png(PIXELS_2X2, 2, 2)
val bytes2 = encode_argb_to_png(PIXELS_2X2, 2, 2)
expect(bytes1).to_equal(bytes2)
```

</details>

### png_encode encode_argb_to_png_rgb

#### 8-bit RGB (color type 2)

#### emits color type 2 and round-trips RGB with alpha restored to 255

- emits color type 2 and round-trips RGB with alpha restored to 255
   - Expected: bytes[25] equals `2u8`
   - Expected: result.is_err() is false
   - Expected: img.pixels equals `PIXELS_2X2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits color type 2 and round-trips RGB with alpha restored to 255")
val bytes = encode_argb_to_png_rgb(PIXELS_2X2, 2, 2)
expect(bytes[25]).to_equal(2u8)
val result = decode_png_to_argb(bytes)
expect(result.is_err()).to_equal(false)
val img = result.unwrap()
# source pixels already carry alpha=0xFF, so RGB round-trip is exact
expect(img.pixels).to_equal(PIXELS_2X2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/image/png_encode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering png_encode encode_argb_to_png, png_encode encode_argb_to_png_rgb.
- png_encode encode_argb_to_png
- png_encode encode_argb_to_png_rgb

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `17615eae97aafeda6fc754b4512ecb34c84259d6f3f2ccfadebbddbe1b521cc4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17615eae97aafeda6fc754b4512ecb34c84259d6f3f2ccfadebbddbe1b521cc4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17615eae97aafeda6fc754b4512ecb34c84259d6f3f2ccfadebbddbe1b521cc4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/image/png_encode_spec.spl
mirror: doc/06_spec/01_unit/lib/common/image/png_encode_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/image/png_encode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/image/png_encode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/image/png_encode_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/image/png_encode_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes back to the exact source pixels via decode_png_to_argb' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/image/png_encode_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with the 8-byte PNG signature' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/image/png_encode_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits an IHDR chunk with exact length, type, width/height, bit depth 8, color type 6' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
