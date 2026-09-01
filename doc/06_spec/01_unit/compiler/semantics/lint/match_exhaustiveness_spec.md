# Match Exhaustiveness Specification

> Tests covering Match Exhaustiveness Lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match Exhaustiveness Specification

## Scenarios

### Match Exhaustiveness Lint

#### exhaustive matches

#### does not flag match with wildcard arm

- does not flag match with wildcard arm
   - Expected: has_warning is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag match with wildcard arm")
val code = "fn classify(x: i64) -> text:\n    match x:\n        case 1: \"one\"\n        case 2: \"two\"\n        case _: \"other\"\n"
val codes = check_match_exhaustiveness_text(code)
val has_warning = codes_contain(codes, "MEXH002")
expect(has_warning).to_equal(false)
```

</details>

#### does not flag match with default catch-all

- does not flag match with default catch-all
   - Expected: has_warning is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag match with default catch-all")
val code = "fn test(x: i64) -> text:\n    match x:\n        case 0: \"zero\"\n        case _: \"nonzero\"\n"
val codes = check_match_exhaustiveness_text(code)
val has_warning = codes_contain(codes, "MEXH002")
expect(has_warning).to_equal(false)
```

</details>

#### non-exhaustive matches

#### flags match without wildcard or default case

- flags match without wildcard or default case
   - Expected: has_warning is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags match without wildcard or default case")
val code = "fn test(x: i64) -> text:\n    match x:\n        case 1: \"one\"\n        case 2: \"two\"\n"
val codes = check_match_exhaustiveness_text(code)
val has_warning = codes_contain(codes, "MEXH002")
expect(has_warning).to_equal(true)
```

</details>

#### flags match with only one case and no default

- flags match with only one case and no default
   - Expected: has_warning is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags match with only one case and no default")
val code = "fn test(x: i64) -> text:\n    match x:\n        case 42: \"the answer\"\n"
val codes = check_match_exhaustiveness_text(code)
val has_warning = codes_contain(codes, "MEXH002")
expect(has_warning).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/match_exhaustiveness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Match Exhaustiveness Lint.
- Match Exhaustiveness Lint

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

- Canonical SPipe generation for source `d99fed9225ffabb7ce692ef478e63a41133009281be88ced1f01466e769fff1c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d99fed9225ffabb7ce692ef478e63a41133009281be88ced1f01466e769fff1c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d99fed9225ffabb7ce692ef478e63a41133009281be88ced1f01466e769fff1c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/lint/match_exhaustiveness_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/lint/match_exhaustiveness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/lint/match_exhaustiveness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/lint/match_exhaustiveness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/lint/match_exhaustiveness_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag match with wildcard arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/match_exhaustiveness_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag match with default catch-all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/match_exhaustiveness_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags match without wildcard or default case' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
