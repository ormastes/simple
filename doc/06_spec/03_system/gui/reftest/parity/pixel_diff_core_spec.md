# Pixel Diff Core Specification

> Tests covering per_channel_delta, pixel_matches, mismatch_ratio, max_channel_delta, bitmap_diff_rect, summarize.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pixel Diff Core Specification

## Scenarios

### per_channel_delta

#### identical pixels give delta 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- identical pixels give delta 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identical pixels give delta 0")
val a = _s(_bm1(100, 150, 200, 255))
val b = _s(_bm1(100, 150, 200, 255))
val d = per_channel_delta(a, b)
expect d to_equal 0
```

</details>

#### single channel differs by 50 gives delta 50

- single channel differs by 50 gives delta 50


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("single channel differs by 50 gives delta 50")
val a = _s(_bm1(100, 0, 0, 0))
val b = _s(_bm1(50, 0, 0, 0))
val d = per_channel_delta(a, b)
expect d to_equal 50
```

</details>

#### returns max across channels

- returns max across channels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns max across channels")
val a = _s(_bm1(255, 10, 0, 0))
val b = _s(_bm1(0, 0, 0, 0))
val d = per_channel_delta(a, b)
expect d to_equal 255
```

</details>

### pixel_matches

#### tolerance >= channel delta returns true

- tolerance >= channel delta returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tolerance >= channel delta returns true")
val a = _s(_bm1(100, 0, 0, 0))
val b = _s(_bm1(98, 0, 0, 0))
val result = pixel_matches(a, b, 2)
expect result to_equal true
```

</details>

#### tolerance < channel delta returns false

- tolerance < channel delta returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tolerance < channel delta returns false")
val a = _s(_bm1(100, 0, 0, 0))
val b = _s(_bm1(97, 0, 0, 0))
val result = pixel_matches(a, b, 2)
expect result to_equal false
```

</details>

### mismatch_ratio

#### identical bitmaps give ratio 0.0

- identical bitmaps give ratio 0.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identical bitmaps give ratio 0.0")
val a = _bm1(128, 64, 32, 255)
val b = _bm1(128, 64, 32, 255)
val r = mismatch_ratio(a, b, 0)
expect r to_equal 0.0
```

</details>

#### 1-pixel differ at tolerance 0 gives ratio 1.0 for 1x1

- 1-pixel differ at tolerance 0 gives ratio 1.0 for 1x1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("1-pixel differ at tolerance 0 gives ratio 1.0 for 1x1")
val a = _bm1(128, 0, 0, 255)
val b = _bm1(127, 0, 0, 255)
val r = mismatch_ratio(a, b, 0)
expect r to_equal 1.0
```

</details>

#### dimension mismatch returns 1.0

- dimension mismatch returns 1.0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dimension mismatch returns 1.0")
val a = BitmapRef.of(1, 1, [0, 0, 0, 255])
val b = BitmapRef.of(2, 1, [0, 0, 0, 255, 0, 0, 0, 255])
val r = mismatch_ratio(a, b, 0)
expect r to_equal 1.0
```

</details>

### max_channel_delta

#### identical bitmaps give 0

- identical bitmaps give 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identical bitmaps give 0")
val a = _bm1(200, 100, 50, 255)
val b = _bm1(200, 100, 50, 255)
val d = max_channel_delta(a, b)
expect d to_equal 0
```

</details>

#### all-red vs all-black 2x2 gives 255

- all-red vs all-black 2x2 gives 255


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all-red vs all-black 2x2 gives 255")
val d = max_channel_delta(_red_2x2(), _black_2x2())
expect d to_equal 255
```

</details>

#### dimension mismatch returns 255

- dimension mismatch returns 255


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dimension mismatch returns 255")
val a = BitmapRef.of(1, 1, [0, 0, 0, 255])
val b = BitmapRef.of(2, 1, [0, 0, 0, 255, 0, 0, 0, 255])
val d = max_channel_delta(a, b)
expect d to_equal 255
```

</details>

### bitmap_diff_rect

#### identical bitmaps return empty rect (0,0,0,0)

- identical bitmaps return empty rect (0,0,0,0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identical bitmaps return empty rect (0,0,0,0)")
val a = _red_2x2()
val b = _red_2x2()
val rect = bitmap_diff_rect(a, b, 0)
expect rect.left to_equal 0
expect rect.top to_equal 0
expect rect.right to_equal 0
expect rect.bottom to_equal 0
```

</details>

#### 2x2 with single differing pixel at (1,1) returns rect covering that pixel

- 2x2 with single differing pixel at (1,1) returns rect covering that pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("2x2 with single differing pixel at (1,1) returns rect covering that pixel")
# Build a 2x2 bitmap: all pixels match except bottom-right (1,1)
val a = BitmapRef.of(2, 2, [
    0, 0, 0, 255,  0, 0, 0, 255,
    0, 0, 0, 255,  0, 0, 0, 255
])
val b = BitmapRef.of(2, 2, [
    0, 0, 0, 255,  0, 0, 0, 255,
    0, 0, 0, 255,  255, 0, 0, 255
])
val rect = bitmap_diff_rect(a, b, 0)
expect rect.left to_equal 1
expect rect.top to_equal 1
expect rect.right to_equal 2
expect rect.bottom to_equal 2
```

</details>

### summarize

#### populates all 4 fields correctly for a 1-pixel difference

- populates all 4 fields correctly for a 1-pixel difference


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("populates all 4 fields correctly for a 1-pixel difference")
val a = _bm1(255, 0, 0, 255)
val b = _bm1(0, 0, 0, 255)
val s = summarize(a, b, 0)
expect s.ratio to_equal 1.0
expect s.max_channel_delta to_equal 255
expect s.mismatched_pixels to_equal 1
expect s.diff_rect.left to_equal 0
expect s.diff_rect.top to_equal 0
expect s.diff_rect.right to_equal 1
expect s.diff_rect.bottom to_equal 1
```

</details>

#### identical bitmaps give zeroed summary

- identical bitmaps give zeroed summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identical bitmaps give zeroed summary")
val a = _bm1(100, 100, 100, 255)
val b = _bm1(100, 100, 100, 255)
val s = summarize(a, b, 0)
expect s.ratio to_equal 0.0
expect s.max_channel_delta to_equal 0
expect s.mismatched_pixels to_equal 0
val empty = s.diff_rect.is_empty()
expect empty to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/reftest/parity/pixel_diff_core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering per_channel_delta, pixel_matches, mismatch_ratio, max_channel_delta, bitmap_diff_rect, summarize.
- per_channel_delta
- pixel_matches
- mismatch_ratio
- max_channel_delta
- bitmap_diff_rect
- summarize

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6db0f2fb9c2d9a5306fa1dbecc4ccc472c0cbf4682cac58147456373c4a6f589`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6db0f2fb9c2d9a5306fa1dbecc4ccc472c0cbf4682cac58147456373c4a6f589`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6db0f2fb9c2d9a5306fa1dbecc4ccc472c0cbf4682cac58147456373c4a6f589`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/reftest/parity/pixel_diff_core_spec.spl
mirror: doc/06_spec/03_system/gui/reftest/parity/pixel_diff_core_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/reftest/parity/pixel_diff_core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/reftest/parity/pixel_diff_core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/reftest/parity/pixel_diff_core_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identical pixels give delta 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/reftest/parity/pixel_diff_core_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single channel differs by 50 gives delta 50' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/reftest/parity/pixel_diff_core_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns max across channels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
