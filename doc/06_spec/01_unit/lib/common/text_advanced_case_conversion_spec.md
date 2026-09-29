# Text Advanced Case Conversion Specification

> Tests covering text_advanced case conversion.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Advanced Case Conversion Specification

## Scenarios

### text_advanced case conversion

#### title-cases each word without leaking numeric char codes

- title-cases each word without leaking numeric char codes
   - Expected: to_title_case("hello world") equals `Hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("title-cases each word without leaking numeric char codes")
expect(to_title_case("hello world")).to_equal("Hello World")
```

</details>

#### snake-cases a PascalCase identifier without leaking numeric char codes

- snake-cases a PascalCase identifier without leaking numeric char codes
   - Expected: to_snake_case("HelloWorld") equals `hello_world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("snake-cases a PascalCase identifier without leaking numeric char codes")
expect(to_snake_case("HelloWorld")).to_equal("hello_world")
```

</details>

#### camel-cases space-separated words without leaking numeric char codes

- camel-cases space-separated words without leaking numeric char codes
   - Expected: to_camel_case("hello world") equals `helloWorld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("camel-cases space-separated words without leaking numeric char codes")
expect(to_camel_case("hello world")).to_equal("helloWorld")
```

</details>

#### camel-cases underscore-separated words too

- camel-cases underscore-separated words too
   - Expected: to_camel_case("hello_world") equals `helloWorld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("camel-cases underscore-separated words too")
expect(to_camel_case("hello_world")).to_equal("helloWorld")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_advanced_case_conversion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text_advanced case conversion.
- text_advanced case conversion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `3b19319a243cc65b9583e5e4a202a05fa821a99f270ef14795b1f70b744934ae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b19319a243cc65b9583e5e4a202a05fa821a99f270ef14795b1f70b744934ae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b19319a243cc65b9583e5e4a202a05fa821a99f270ef14795b1f70b744934ae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/text_advanced_case_conversion_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_advanced_case_conversion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_advanced_case_conversion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_advanced_case_conversion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_advanced_case_conversion_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'title-cases each word without leaking numeric char codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_advanced_case_conversion_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'snake-cases a PascalCase identifier without leaking numeric char codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_advanced_case_conversion_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'camel-cases space-separated words without leaking numeric char codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
