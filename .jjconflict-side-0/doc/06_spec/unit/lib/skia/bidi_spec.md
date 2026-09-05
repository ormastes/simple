# Bidi Specification

> Tests covering classify_bidi: character class detection, is_rtl: primary direction detection, compute_embedding_levels: pure LTR text.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bidi Specification

## Scenarios

### classify_bidi: character class detection

#### ASCII 'A' (U+0041 = 65) returns L

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ASCII 'A' (U+0041 = 65) returns L


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ASCII 'A' (U+0041 = 65) returns L")
val cls = classify_bidi(65)
expect cls to_equal BidiClass.L
```

</details>

#### Hebrew alef (U+05D0 = 1488) returns R

- Hebrew alef (U+05D0 = 1488) returns R


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Hebrew alef (U+05D0 = 1488) returns R")
val cls = classify_bidi(1488)
expect cls to_equal BidiClass.R
```

</details>

#### Arabic alif (U+0627 = 1575) returns AL

- Arabic alif (U+0627 = 1575) returns AL


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Arabic alif (U+0627 = 1575) returns AL")
val cls = classify_bidi(1575)
expect cls to_equal BidiClass.AL
```

</details>

#### ASCII digit '0' (U+0030 = 48) returns EN

- ASCII digit '0' (U+0030 = 48) returns EN


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ASCII digit '0' (U+0030 = 48) returns EN")
val cls = classify_bidi(48)
expect cls to_equal BidiClass.EN
```

</details>

#### ASCII space (U+0020 = 32) returns ON

- ASCII space (U+0020 = 32) returns ON


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ASCII space (U+0020 = 32) returns ON")
val cls = classify_bidi(32)
expect cls to_equal BidiClass.ON
```

</details>

### is_rtl: primary direction detection

#### sequence starting with Latin 'A' returns false

- sequence starting with Latin 'A' returns false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sequence starting with Latin 'A' returns false")
val cps: [i64] = [65, 66, 67]
val result = is_rtl(cps)
expect result to_equal false
```

</details>

#### sequence starting with Hebrew alef (1488) returns true

- sequence starting with Hebrew alef (1488) returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sequence starting with Hebrew alef (1488) returns true")
val cps: [i64] = [1488, 1489, 1490]
val result = is_rtl(cps)
expect result to_equal true
```

</details>

### compute_embedding_levels: pure LTR text

#### pure ASCII Latin text with base LTR produces all level 0

- pure ASCII Latin text with base LTR produces all level 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pure ASCII Latin text with base LTR produces all level 0")
# 'A'=65, 'B'=66, 'C'=67
val cps: [i64] = [65, 66, 67]
val levels = compute_embedding_levels(cps, false)
val l0 = levels[0]
val l1 = levels[1]
val l2 = levels[2]
expect l0 to_equal 0
expect l1 to_equal 0
expect l2 to_equal 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/skia/bidi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering classify_bidi: character class detection, is_rtl: primary direction detection, compute_embedding_levels: pure LTR text.
- classify_bidi: character class detection
- is_rtl: primary direction detection
- compute_embedding_levels: pure LTR text

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

- Canonical SPipe generation for source `da526722ae5de2e6d634a7ed6f7bc98e67a7c0f035d9ad49d3112c9b5bbb269c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da526722ae5de2e6d634a7ed6f7bc98e67a7c0f035d9ad49d3112c9b5bbb269c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da526722ae5de2e6d634a7ed6f7bc98e67a7c0f035d9ad49d3112c9b5bbb269c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/skia/bidi_spec.spl
mirror: doc/06_spec/unit/lib/skia/bidi_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/skia/bidi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/skia/bidi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/skia/bidi_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ASCII 'A' (U+0041 = 65) returns L' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/bidi_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Hebrew alef (U+05D0 = 1488) returns R' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/bidi_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Arabic alif (U+0627 = 1575) returns AL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
