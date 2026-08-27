# Template Kind Can Follow Specification

> Tests covering kind_can_follow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Template Kind Can Follow Specification

## Scenarios

### kind_can_follow

#### allows any fragment kind to start a matcher (no previous kind)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows any fragment kind to start a matcher (no previous kind)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows any fragment kind to start a matcher (no previous kind)")
kind_can_follow(FragmentKind.Expr, nil) == true
```

</details>

#### forbids anything from directly following an expr fragment

- forbids anything from directly following an expr fragment


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("forbids anything from directly following an expr fragment")
kind_can_follow(FragmentKind.Ident, FragmentKind.Expr) == false
```

</details>

#### forbids anything from directly following a stmt fragment

- forbids anything from directly following a stmt fragment


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("forbids anything from directly following a stmt fragment")
kind_can_follow(FragmentKind.Ident, FragmentKind.Stmt) == false
```

</details>

#### allows a fragment to follow an unambiguous fragment kind

- allows a fragment to follow an unambiguous fragment kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("allows a fragment to follow an unambiguous fragment kind")
kind_can_follow(FragmentKind.Ident, FragmentKind.Ty) == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/macros/template_kind_can_follow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kind_can_follow.
- kind_can_follow

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `50c9a01cfb072b632eb2ae857398b5b2ac96bb4f7aaadce88eb3a8aa42ff116f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `50c9a01cfb072b632eb2ae857398b5b2ac96bb4f7aaadce88eb3a8aa42ff116f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `50c9a01cfb072b632eb2ae857398b5b2ac96bb4f7aaadce88eb3a8aa42ff116f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/macros/template_kind_can_follow_spec.spl
mirror: doc/06_spec/01_unit/compiler/macros/template_kind_can_follow_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/macros/template_kind_can_follow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/macros/template_kind_can_follow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/macros/template_kind_can_follow_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/compiler/macros/template_kind_can_follow_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows any fragment kind to start a matcher (no previous kind)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/macros/template_kind_can_follow_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forbids anything from directly following an expr fragment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/macros/template_kind_can_follow_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forbids anything from directly following a stmt fragment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
