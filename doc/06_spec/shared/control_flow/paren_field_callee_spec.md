# Paren Field Callee Specification

> Tests covering parenthesized field callee, self receiver, local-variable receiver, lambda-valued fields, arity and nesting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Paren Field Callee Specification

## Scenarios

### parenthesized field callee

### self receiver

#### resolves a function-typed field called through parentheses

- resolves a function-typed field called through parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("resolves a function-typed field called through parentheses")
val d = Doubler(cb: double)
expect d.via_paren(5) == 10
```

</details>

#### agrees with the unparenthesized call

- agrees with the unparenthesized call


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("agrees with the unparenthesized call")
val d = Doubler(cb: double)
expect d.via_paren(7) == d.via_plain(7)
```

</details>

#### agrees with binding the field to a local first

- agrees with binding the field to a local first


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("agrees with binding the field to a local first")
val d = Doubler(cb: double)
expect d.via_paren(9) == d.via_bound_local(9)
```

</details>

### local-variable receiver

#### resolves a field call through parentheses on a plain local

- resolves a field call through parentheses on a plain local


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("resolves a field call through parentheses on a plain local")
val d = Doubler(cb: double)
expect (d.cb)(5) == 10
```

</details>

#### agrees with the unparenthesized call on a plain local

- agrees with the unparenthesized call on a plain local


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("agrees with the unparenthesized call on a plain local")
val d = Doubler(cb: double)
expect (d.cb)(6) == d.cb(6)
```

</details>

### lambda-valued fields

#### resolves a lambda-valued field called through parentheses

- resolves a lambda-valued field called through parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("resolves a lambda-valued field called through parentheses")
val d = Doubler(cb: |v: i64| v * 2)
expect d.via_paren(21) == 42
```

</details>

#### agrees with the unparenthesized call for a lambda-valued field

- agrees with the unparenthesized call for a lambda-valued field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("agrees with the unparenthesized call for a lambda-valued field")
val d = Doubler(cb: |v: i64| v * 2)
expect d.via_paren(8) == d.via_plain(8)
```

</details>

### arity and nesting

#### forwards multiple arguments to a grouped field callee

- forwards multiple arguments to a grouped field callee


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("forwards multiple arguments to a grouped field callee")
val t = TwoFields(add_fn: add2, neg_fn: negate)
expect (t.add_fn)(3, 4) == 7
```

</details>

#### resolves a grouped field callee nested inside another

- resolves a grouped field callee nested inside another


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SHARED
step("resolves a grouped field callee nested inside another")
val t = TwoFields(add_fn: add2, neg_fn: negate)
expect t.combine(3, 4) == 0 - 7
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/control_flow/paren_field_callee_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering parenthesized field callee, self receiver, local-variable receiver, lambda-valued fields, arity and nesting.
- parenthesized field callee
- self receiver
- local-variable receiver
- lambda-valued fields
- arity and nesting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SHARED`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c81b1d10f6671d93bcc4495e472defd67ac0d4962942be2207299e571a40db3d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c81b1d10f6671d93bcc4495e472defd67ac0d4962942be2207299e571a40db3d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c81b1d10f6671d93bcc4495e472defd67ac0d4962942be2207299e571a40db3d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/shared/control_flow/paren_field_callee_spec.spl
mirror: doc/06_spec/shared/control_flow/paren_field_callee_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/shared/control_flow/paren_field_callee_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/shared/control_flow/paren_field_callee_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/shared/control_flow/paren_field_callee_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a function-typed field called through parentheses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/control_flow/paren_field_callee_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the unparenthesized call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/shared/control_flow/paren_field_callee_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with binding the field to a local first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
