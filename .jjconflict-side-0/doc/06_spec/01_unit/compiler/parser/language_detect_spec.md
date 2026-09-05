# Language Detect Specification

> Tests covering DetectionResult, LanguageDetector.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Language Detect Specification

## Scenarios

### DetectionResult

#### creates detection result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates detection result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates detection result")
val result = DetectionResult.new(language: "simple", confidence: 0.95)
expect result.language == "simple"
expect result.confidence == 0.95
```

</details>

#### ranks by confidence

- ranks by confidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ranks by confidence")
val results = [
    DetectionResult.new(language: "rust", confidence: 0.8),
    DetectionResult.new(language: "python", confidence: 0.95),
    DetectionResult.new(language: "simple", confidence: 0.9)
]
# Check that highest confidence result exists
expect results[1].confidence == 0.95
```

</details>

### LanguageDetector

#### detects Python

- detects Python


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects Python")
val detector = LanguageDetector.new()
check(true)
```

</details>

#### detects Rust

- detects Rust


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects Rust")
val detector = LanguageDetector.new()
check(true)
```

</details>

#### detects Simple

- detects Simple


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects Simple")
val detector = LanguageDetector.new()
check(true)
```

</details>

#### handles unknown languages

- handles unknown languages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unknown languages")
val detector = LanguageDetector.new()
check(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/language_detect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DetectionResult, LanguageDetector.
- DetectionResult
- LanguageDetector

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `58d25267b41529b0f96f231c27c45ae62180e7a63b755e815560b278ffe6027a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58d25267b41529b0f96f231c27c45ae62180e7a63b755e815560b278ffe6027a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58d25267b41529b0f96f231c27c45ae62180e7a63b755e815560b278ffe6027a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/parser/language_detect_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/language_detect_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/parser/language_detect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/language_detect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/language_detect_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates detection result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/language_detect_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ranks by confidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/language_detect_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects Python' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
