# Diagnostics must not recommend the implicit-self field ASSIGNMENT form

> Inside a method body, a bare `field = value` (no `self.`) does **not** assign the receiver's field. Every lane rejects it: HIR lowering reports `unresolved name`, MIR reports `assignment target has no local binding`, the pure-Simple interpreter reports `undefined variable`, and the Rust seed's AST interpreter now reports `invalid assignment: ... is a field of ...` rather than minting a fresh local that shadows the field.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Diagnostics must not recommend the implicit-self field ASSIGNMENT form

Inside a method body, a bare `field = value` (no `self.`) does **not** assign the receiver's field. Every lane rejects it: HIR lowering reports `unresolved name`, MIR reports `assignment target has no local binding`, the pure-Simple interpreter reports `undefined variable`, and the Rust seed's AST interpreter now reports `invalid assignment: ... is a field of ...` rather than minting a fresh local that shadows the field.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Diagnostics / Parser error recovery |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Inside a method body, a bare `field = value` (no `self.`) does **not** assign
the receiver's field. Every lane rejects it: HIR lowering reports
`unresolved name`, MIR reports `assignment target has no local binding`, the
pure-Simple interpreter reports `undefined variable`, and the Rust seed's AST
interpreter now reports `invalid assignment: ... is a field of ...` rather than
minting a fresh local that shadows the field.

The compounding defect was that the parser's `JavaThis` recovery hint — shown
when a user coming from Java/JavaScript writes `this.x = value` — recommended
exactly the broken shape:

```text
Java:    this.x = value;
Simple:  x = value  # self is implicit
```

Following the compiler's own advice therefore produced a silent wrong result
(and, after the guard landed, a hard error). "Implicit self" means omitting
`self` from the **parameter list**, not from **field access**; the correct
advice is `self.x = value`.

These assertions read the two recovery sources directly, because the hint text
is the artifact under test — a behavioural test would only re-prove the
lowering guard, which lives in a different lane.

## Scenarios

### JavaThis recovery hint recommends explicit self for field assignment

#### does not recommend the bare implicit-self assignment form

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### recommends self.x = value in the JavaThis worked example

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file(RUST_RECOVERY)
assert_true(src.contains("Simple:  self.x = value"))
```

</details>

#### states that self is implicit only in the parameter list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file(RUST_RECOVERY)
assert_true(src.contains("implicit only in the parameter list"))
```

</details>

#### gives the same explicit-self advice in the pure-Simple recovery port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_file(SIMPLE_RECOVERY)
assert_true(src.contains("self.x = value"))
```

</details>

#### keeps the ExplicitSelf hint scoped to the parameter list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This hint is CORRECT and must not be broadened into field access:
# dropping `self` from the parameter list is right, dropping it from
# `self.field` is the bug.
val src = read_file(RUST_RECOVERY)
assert_true(src.contains("The 'self' parameter is implicit in methods"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `511aee563df123e180d5d181c90cb3c33b37259df700edd94d76889986010c19`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `511aee563df123e180d5d181c90cb3c33b37259df700edd94d76889986010c19`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `511aee563df123e180d5d181c90cb3c33b37259df700edd94d76889986010c19`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.spl:51:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not recommend the bare implicit-self assignment form' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.spl:59:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'recommends self.x = value in the JavaThis worked example' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.spl:63:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'states that self is implicit only in the parameter list' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/frontend/implicit_self_field_assignment_hint_spec.spl:67:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'gives the same explicit-self advice in the pure-Simple recovery port' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
