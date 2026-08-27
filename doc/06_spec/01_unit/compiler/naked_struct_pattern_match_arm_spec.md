# A naked `case StructName(...)` arm must not be an unconditional match

> A `match` arm whose pattern is a bare struct constructor — `case PId(raw):`, with no `Some(...)` wrapper — is lowered by the Rust seed to the *literal* `true` (`hir/lower/stmt_lowering.rs:1679`, `is_class_pattern` → `HirExprKind::Bool(true)`). There is no discriminant compare, no type test and no nil guard, so such an arm matches **every** scrutinee: a value of an unrelated struct type, and `nil`. Every later arm, including `case _:`, becomes dead code.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# A naked `case StructName(...)` arm must not be an unconditional match

A `match` arm whose pattern is a bare struct constructor — `case PId(raw):`, with no `Some(...)` wrapper — is lowered by the Rust seed to the *literal* `true` (`hir/lower/stmt_lowering.rs:1679`, `is_class_pattern` → `HirExprKind::Bool(true)`). There is no discriminant compare, no type test and no nil guard, so such an arm matches **every** scrutinee: a value of an unrelated struct type, and `nil`. Every later arm, including `case _:`, becomes dead code.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Pattern matching / match-arm selection |
| Status | Active |
| Source | `test/01_unit/compiler/naked_struct_pattern_match_arm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A `match` arm whose pattern is a bare struct constructor — `case PId(raw):`,
with no `Some(...)` wrapper — is lowered by the Rust seed to the *literal*
`true` (`hir/lower/stmt_lowering.rs:1679`, `is_class_pattern` →
`HirExprKind::Bool(true)`). There is no discriminant compare, no type test and
no nil guard, so such an arm matches **every** scrutinee: a value of an
unrelated struct type, and `nil`. Every later arm, including `case _:`,
becomes dead code.

The originally filed polarity ("the naked arm always falls to the wildcard")
is the inverse and does not reproduce. It looked that way because a naked arm
carrying a *binding* selects on `nil` and then traps reading a field off nil
(`runtime error: field access on nil receiver`, SIGILL) — an arm that selects
and then dies is externally indistinguishable from an arm that never selected.

This is the `fb1a0033d51` family: a `case` arm existing is not evidence it
ever runs, and here it is the **wildcard** arm that never runs.

## Coverage

The bind-free patterns are load-bearing: they observe arm *selection* only, so
a failure cannot be confused with a destructuring fault.

- `nil` must reach the wildcard, not the struct arm.
- A `Beta` pattern must not swallow an `Alpha` value.
- The `Some(...)` form is the control — it is correct on the buggy lane too,
  so a red control means the harness, not the defect.

## Scenarios

### naked struct-constructor match arms

#### selects the struct arm for a present value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### falls through to the wildcard for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(select_naked(nil), "WILDCARD")
```

</details>

#### does not let a Beta pattern swallow an Alpha value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(select_wrong_type_first(Alpha(a: 7)), "ALPHA")
```

</details>

#### does not let a Beta pattern swallow nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(select_wrong_type_first(nil), "WILDCARD")
```

</details>

#### binds the payload for a present value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(select_naked_binding(Alpha(a: 7)), "ALPHA:7")
```

</details>

#### keeps the Some(...) control form correct for a present value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(select_some(Alpha(a: 7)), "ALPHA")
```

</details>

#### keeps the Some(...) control form correct for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(select_some(nil), "WILDCARD")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `ae3a4fcaf6f216419672786e963405bf6af55f3c7f72b85c5910273ec5599d41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae3a4fcaf6f216419672786e963405bf6af55f3c7f72b85c5910273ec5599d41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae3a4fcaf6f216419672786e963405bf6af55f3c7f72b85c5910273ec5599d41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/naked_struct_pattern_match_arm_spec.spl
mirror: doc/06_spec/01_unit/compiler/naked_struct_pattern_match_arm_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/naked_struct_pattern_match_arm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/naked_struct_pattern_match_arm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/naked_struct_pattern_match_arm_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/naked_struct_pattern_match_arm_spec.spl:95:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'selects the struct arm for a present value' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/naked_struct_pattern_match_arm_spec.spl:100:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'falls through to the wildcard for nil' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/naked_struct_pattern_match_arm_spec.spl:103:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not let a Beta pattern swallow an Alpha value' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/naked_struct_pattern_match_arm_spec.spl:106:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not let a Beta pattern swallow nil' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
