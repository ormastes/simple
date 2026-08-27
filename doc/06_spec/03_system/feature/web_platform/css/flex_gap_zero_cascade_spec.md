# CSS flex gap zero cascade

> This scenario proves both that a later valid `gap:0` declaration resets an earlier positive Flex gap and that a later malformed declaration does not erase an earlier valid `gap:4px`. Both cases cross the dispatch and full Style reconstruction paths; an invalid-only row remains the zero-gap control.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS flex gap zero cascade

This scenario proves both that a later valid `gap:0` declaration resets an earlier positive Flex gap and that a later malformed declaration does not erase an earlier valid `gap:4px`. Both cases cross the dispatch and full Style reconstruction paths; an invalid-only row remains the zero-gap control.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/css_gap_zero_cascade.md |
| Source | `test/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario proves both that a later valid `gap:0` declaration resets an
earlier positive Flex gap and that a later malformed declaration does not
erase an earlier valid `gap:4px`. Both cases cross the dispatch and full Style
reconstruction paths; an invalid-only row remains the zero-gap control.

All rows lower through shared Web semantic/layout state into the existing
canonical `DrawIrComposition` and Engine2D executor. No private painter,
parallel Web IR, Draw IR command, or backend path is introduced.

## Standards contract

CSS Box Alignment admits zero as a non-negative gap. A valid later declaration
wins, while a malformed declaration is discarded before winner selection.
Malformed-only and negative gaps remain outside the accepted subset.

## Exact fixture

The viewport is 12 by 22 pixels. The first two 12-by-2 Flex rows reset a 4px
stylesheet gap to zero. The next two retain `gap:4px` before a malformed
duplicate through the dispatch and full reconstruction paths. Further rows
reject signed, decimal, foreign-unit, and trailing-junk values, reset
`initial`/`unset`, reset a positive class at terminal parent-default `inherit`
through both declaration paths, and keep invalid-only controls at zero.

General nonzero inherited gaps remain RED until computed parent gap state is
available. `revert` and `revert-layer` also remain RED until origin and layer
state is represented; this scenario does not approximate either keyword.

## Evidence boundary

The SSpec asserts parsed nodes, computed gap fields, exact semantic boxes,
canonical Draw IR rectangle geometry and color, zero skipped commands, and
all 264 framebuffer pixels. Runtime PASS is claimed only after a qualified
pure-Simple execution; static review alone is not runtime evidence.

## Scenarios

### REQ-WEB-BROWSER-003/004/021: CSS gap zero cascade

#### should reset positive Flex gaps through both declaration paths

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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/css_gap_zero_cascade.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003/004/021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6776f4067e9b779412f184cc5800e3e774745db0fcdbf235d456e7c493aba95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6776f4067e9b779412f184cc5800e3e774745db0fcdbf235d456e7c493aba95`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6776f4067e9b779412f184cc5800e3e774745db0fcdbf235d456e7c493aba95`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=85 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.spl:168:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should reset positive Flex gaps through both declaration paths' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.spl:168:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reset positive Flex gaps through both declaration paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
