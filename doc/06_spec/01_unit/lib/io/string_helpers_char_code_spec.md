# String Helpers Char Code Specification

> Tests covering io string helpers char_code.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# String Helpers Char Code Specification

## Scenarios

### io string helpers char_code

#### returns real ASCII codes for letters in all three tiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### returns the code point of a digit, not its parsed value

- query digit '7' — code 55, not the number 7
   - Expected: gc_char_code("7") equals `55`
   - Expected: nogc_char_code("0") equals `48`
   - Expected: sync_char_code("9") equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: LIB-IO-CHARCODE-002
# @manual_section: 3.2
step("query digit '7' — code 55, not the number 7")
expect(gc_char_code("7")).to_equal(55)
expect(nogc_char_code("0")).to_equal(48)
expect(sync_char_code("9")).to_equal(57)
```

</details>

#### returns 0 only for the empty string

- empty input yields the documented 0 sentinel
   - Expected: gc_char_code("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: LIB-IO-CHARCODE-003
# @manual_section: 3.2
step("empty input yields the documented 0 sentinel")
expect(gc_char_code("")).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/string_helpers_char_code_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering io string helpers char_code.
- io string helpers char_code

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `b096c1973682138592cc7fb0116e11fd134ac3b762d96e205dc407048c10bf84`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b096c1973682138592cc7fb0116e11fd134ac3b762d96e205dc407048c10bf84`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b096c1973682138592cc7fb0116e11fd134ac3b762d96e205dc407048c10bf84`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/io/string_helpers_char_code_spec.spl
mirror: doc/06_spec/01_unit/lib/io/string_helpers_char_code_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/io/string_helpers_char_code_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/io/string_helpers_char_code_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/io/string_helpers_char_code_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/io/string_helpers_char_code_spec.spl:19:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns real ASCII codes for letters in all three tiers' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/io/string_helpers_char_code_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the code point of a digit, not its parsed value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/string_helpers_char_code_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns 0 only for the empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
