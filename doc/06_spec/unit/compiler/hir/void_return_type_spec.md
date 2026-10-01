# Void Return Type Specification

> Tests covering void resolves as the unit type in HIR lowering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Void Return Type Specification

## Scenarios

### void resolves as the unit type in HIR lowering

#### accepts `-> void` on a local function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### accepts `-> void` on an imported sibling signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_void_chain([
    "pkg.sib|fn walk(line: i64) -> void:\n    val x = line",
    "pkg.__init__|use pkg.sib.\{walk\}\nexport walk"])
expect(diagnostics).to_equal("")
```

</details>

#### accepts `void` as a generic argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_void_chain([
    "pkg.gen|fn make() -> Result<void, text>:\n    Ok(())"])
expect(diagnostics).to_equal("")
```

</details>

#### still accepts `unit` identically

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diagnostics = lower_void_chain([
    "pkg.unit|fn walk(line: i64) -> unit:\n    val x = line"])
expect(diagnostics).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/void_return_type_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering void resolves as the unit type in HIR lowering.
- void resolves as the unit type in HIR lowering

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

- Canonical SPipe generation for source `ae6d29884b707f32c9e476daec0c8ce0bea4cfd209e6ca1fcea41c4fb1dbcc05`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae6d29884b707f32c9e476daec0c8ce0bea4cfd209e6ca1fcea41c4fb1dbcc05`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae6d29884b707f32c9e476daec0c8ce0bea4cfd209e6ca1fcea41c4fb1dbcc05`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/compiler/hir/void_return_type_spec.spl
mirror: doc/06_spec/unit/compiler/hir/void_return_type_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/void_return_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/void_return_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/void_return_type_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/compiler/hir/void_return_type_spec.spl:50:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts `-> void` on a local function' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/hir/void_return_type_spec.spl:58:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts `-> void` on an imported sibling signature' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/hir/void_return_type_spec.spl:65:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts `void` as a generic argument' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/hir/void_return_type_spec.spl:71:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'still accepts `unit` identically' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
