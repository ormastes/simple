# Html Widget Numeric Guard Specification

> Tests covering html widget numeric guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Widget Numeric Guard Specification

## Scenarios

### html widget numeric guards

#### guards widget property integer parsing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards widget property integer parsing
   - Expected: html_int_or("notanumber", -1) equals `-1`
   - Expected: html_int_or("", 0) equals `0`
   - Expected: html_int_or("   ", 0) equals `0`
   - Expected: html_int_or("12x", -1) equals `-1`
   - Expected: html_int_or("-", 0) equals `0`
   - Expected: html_int_or("-7", -1) equals `-7`
   - Expected: html_int_or(" 42 ", -1) equals `42`
   - Expected: html_int_or("0", -1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guards widget property integer parsing")
# oracle: malformed widget property text must fall back to the caller default
expect(html_int_or("notanumber", -1)).to_equal(-1)
expect(html_int_or("", 0)).to_equal(0)
expect(html_int_or("   ", 0)).to_equal(0)
expect(html_int_or("12x", -1)).to_equal(-1)
expect(html_int_or("-", 0)).to_equal(0)
# oracle: signed and plain decimal text parse exactly; whitespace trimmed
expect(html_int_or("-7", -1)).to_equal(-7)
expect(html_int_or(" 42 ", -1)).to_equal(42)
expect(html_int_or("0", -1)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/html_widget_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering html widget numeric guards.
- html widget numeric guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2a35db9f41a154451764a0457a4ae4475bdae1353fa98476ac4c229c95013cad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a35db9f41a154451764a0457a4ae4475bdae1353fa98476ac4c229c95013cad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a35db9f41a154451764a0457a4ae4475bdae1353fa98476ac4c229c95013cad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/app/ui/html_widget_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/ui/html_widget_numeric_guard_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/html_widget_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/html_widget_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/html_widget_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/ui/html_widget_numeric_guard_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards widget property integer parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
