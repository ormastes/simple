# Web Css Specification

> Tests covering bounded tiny CSS declarations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Css Specification

## Scenarios

### bounded tiny CSS declarations

#### parses tag class and ID selectors with admitted properties

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### reports unsupported selectors and properties explicitly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = tiny_css_parse("div > p { color: red } p { transform: rotate(1deg); width: 10px }", 4, 8)
expect(parsed.status.is_ok()).to_be(false)
expect(parsed.unsupported_count).to_equal(2)
expect(parsed.declarations.len()).to_equal(1)
```

</details>

#### enforces rule and declaration bounds and malformed syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tiny_css_parse("p { color: red } div { color: blue }", 1, 8).status.is_ok()).to_be(false)
expect(tiny_css_parse("p { color: red; width: 1px }", 2, 1).status.is_ok()).to_be(false)
expect(tiny_css_parse("p color: red", 2, 2).status.is_ok()).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/web_css_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded tiny CSS declarations.
- bounded tiny CSS declarations

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

- Canonical SPipe generation for source `9c58a7a4b363708faf4d3416c17ad518c6242980bb1280aeb2f2151adad8d25d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c58a7a4b363708faf4d3416c17ad518c6242980bb1280aeb2f2151adad8d25d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c58a7a4b363708faf4d3416c17ad518c6242980bb1280aeb2f2151adad8d25d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/lib/tiny/web_css_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/web_css_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=70 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/web_css_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/web_css_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/web_css_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/tiny/web_css_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/web_css_spec.spl:13:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'parses tag class and ID selectors with admitted properties' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_css_spec.spl:23:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports unsupported selectors and properties explicitly' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/web_css_spec.spl:29:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'enforces rule and declaration bounds and malformed syntax' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
