# Match: non-binding sub-patterns inside an enum payload must test and bind

> Inside an enum pattern's payload, only `Binding` and `Wildcard` sub-patterns are honoured. Every other sub-pattern kind -- a nested `Enum` (`case W(A(n))`), or a `Literal` (`case X(5)`) -- is treated as **always-match** and binds nothing:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Match: non-binding sub-patterns inside an enum payload must test and bind

Inside an enum pattern's payload, only `Binding` and `Wildcard` sub-patterns are honoured. Every other sub-pattern kind -- a nested `Enum` (`case W(A(n))`), or a `Literal` (`case X(5)`) -- is treated as **always-match** and binds nothing:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Semantics / Pattern matching |
| Status | Active |
| Source | `test/01_unit/compiler/enum_payload_subpattern_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Inside an enum pattern's payload, only `Binding` and `Wildcard` sub-patterns are
honoured. Every other sub-pattern kind -- a nested `Enum` (`case W(A(n))`), or a
`Literal` (`case X(5)`) -- is treated as **always-match** and binds nothing:

- the sub-pattern's **test is skipped**, so an arm fires on values it must
  reject (`case E.I(5)` matches `E.I(7)`), and
- the sub-pattern's **bindings are never registered**, so names inside it read
  `0` instead of the payload value.

Both failures are **silent**: the program compiles and exits 0 with wrong
numbers, which is why these assertions check printed/returned VALUES rather than
an exit code or a diagnostic.

Depth-1 bindings (`case E.I(n)`) and top-level literals (`case 7:` on a bare
i64) are unaffected and are asserted here as controls, so a regression in this
spec localises to the enum-payload sub-pattern walk specifically.

## This spec is GREEN on the lane that runs it -- read the bug doc

The defect is **engine-specific**, and the spec runner is on the good engine:

| lane | enum-payload literal / nested-enum sub-pattern |
|---|---|
| `bin/simple_seed test` (tree-walking interpreter) | correct -- this spec passes |
| `bin/simple_seed run` (JIT) | **wrong** |
| pure-Simple `native-build --backend llvm` | **wrong** |

So a green result here is **not** evidence the defect is fixed; it only proves
the interpreter matcher still recurses. The wrong value is also not a stable
sentinel -- `0`, `32` and a raw pointer were all observed, and one shape
coincidentally produced the correct answer -- so spot-checks are not evidence
either. Reproduce on a compiled lane using the probes recorded in the bug doc.

This spec becomes an active gate once the runner executes on the native/JIT
engine; until then it is a forward-looking guard.

## Syntax

```simple
match E.I(7):
    case E.I(5): ...   # must NOT fire -- nested literal test
    case E.I(7): ...   # must fire

match Outer.W(Inner.A(7)):
    case Outer.W(Inner.A(n)): ...   # n must be 7, not 0
```

## Scenarios

### enum payload sub-patterns

#### binds a depth-1 enum payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### binds every slot of a depth-1 multi-arity payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(d1_tuple_arity2(), 2122)
```

</details>

#### tests a top-level literal pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(toplevel_literal(), 7)
```

</details>

#### does not match an int literal sub-pattern against a different int

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_literal_int(), 7)
```

</details>

#### does not match a text literal sub-pattern against a different text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_literal_text(), 1)
```

</details>

#### does not match a bool literal sub-pattern against a different bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_literal_bool(), 1)
```

</details>

#### gates on a literal slot while binding its sibling slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(literal_and_binding_siblings(), 72)
```

</details>

#### binds a name inside a nested enum sub-pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_enum_binds(), 41)
```

</details>

#### selects the arm whose nested enum variant actually matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_enum_selects_right_arm(), 1)
```

</details>

#### binds through three levels of nesting

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_enum_depth3(), 51)
```

</details>

#### reaches a nested enum arm that is not the first arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_enum_third_arm(), 151)
```

</details>

#### binds when the nested sub-pattern is last among siblings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_last_of_two(), 71072)
```

</details>

#### binds when the nested sub-pattern is first among siblings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_first_of_two(), 81082)
```

</details>

#### binds every slot of a multi-arity nested payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(nested_inner_arity2(), 101102)
```

</details>

#### binds inside a nested sub-pattern alongside wildcards

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(wildcard_outer_binding_inner(), 123)
```

</details>

#### resolves an inner variant that shares the outer variant's name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(shared_variant_name(), 141)
```

</details>

#### evaluates a guard over a nested binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(guard_over_nested_binding(), 9)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `7494c671c0aa2dd43ce0408d7eefb049b75fad8c20ab6a73ff181ae437db9613`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7494c671c0aa2dd43ce0408d7eefb049b75fad8c20ab6a73ff181ae437db9613`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7494c671c0aa2dd43ce0408d7eefb049b75fad8c20ab6a73ff181ae437db9613`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/enum_payload_subpattern_spec.spl
mirror: doc/06_spec/01_unit/compiler/enum_payload_subpattern_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/enum_payload_subpattern_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/enum_payload_subpattern_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/enum_payload_subpattern_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/enum_payload_subpattern_spec.spl:213:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'binds a depth-1 enum payload' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/enum_payload_subpattern_spec.spl:218:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'binds every slot of a depth-1 multi-arity payload' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/enum_payload_subpattern_spec.spl:221:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'tests a top-level literal pattern' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/enum_payload_subpattern_spec.spl:225:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not match an int literal sub-pattern against a different int' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
