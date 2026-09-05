# CSS Flex RTL Main Axis

> This bounded integer-pixel scenario proves that `direction` reverses the row

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Flex RTL Main Axis

This bounded integer-pixel scenario proves that `direction` reverses the row

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/flex_rtl_main_axis_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This bounded integer-pixel scenario proves that `direction` reverses the row
flex main axis without changing DOM/order sorting, through canonical Web
semantics, layout, Draw IR, and Engine2D.

## Scenarios

### REQ-WEB-BROWSER-003/004/021: CSS RTL row-flex main axis

#### should place ordered children from main-start for RTL and LTR

**Scenario capture:** artifact after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WEB-BROWSER-003/004/021
```

</details>

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

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003/004/021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f256e1b4466848c02cf6b70e2e978f9d8029f1dc362914ce96b9d9dc0cc5a75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f256e1b4466848c02cf6b70e2e978f9d8029f1dc362914ce96b9d9dc0cc5a75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f256e1b4466848c02cf6b70e2e978f9d8029f1dc362914ce96b9d9dc0cc5a75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/web_platform/css/flex_rtl_main_axis_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/flex_rtl_main_axis_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=85 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/feature/web_platform/css/flex_rtl_main_axis_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/flex_rtl_main_axis_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/flex_rtl_main_axis_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/web_platform/css/flex_rtl_main_axis_spec.spl:108:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should place ordered children from main-start for RTL and LTR' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/flex_rtl_main_axis_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should place ordered children from main-start for RTL and LTR' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
