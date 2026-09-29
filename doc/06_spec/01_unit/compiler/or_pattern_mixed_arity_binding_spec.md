# An or-pattern with mixed-arity alternatives must bind from the alternative

> `build_pattern_binding_stmts` normalized `Pattern::Or` to its FIRST alternative, on the theory that "every alternative binds the same names". Binding the same NAMES does not imply binding them from the same payload SLOT. So

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# An or-pattern with mixed-arity alternatives must bind from the alternative

`build_pattern_binding_stmts` normalized `Pattern::Or` to its FIRST alternative, on the theory that "every alternative binds the same names". Binding the same NAMES does not imply binding them from the same payload SLOT. So

## At a Glance

| Field | Value |
|-------|-------|
| Category | HIR lowering / pattern bindings |
| Status | Active |
| Source | `test/01_unit/compiler/or_pattern_mixed_arity_binding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`build_pattern_binding_stmts` normalized `Pattern::Or` to its FIRST alternative,
on the theory that "every alternative binds the same names". Binding the same
NAMES does not imply binding them from the same payload SLOT. So

    case Ptr(inner, _) | Ref(inner, _) | Slice(inner):

selected correctly for `Slice(7)` and then extracted `inner` using `Ptr`'s
two-field shape, yielding **3** instead of 7 — no error, no warning. The
arity-2 alternatives were correct, which is what made it hide: two of the three
inputs looked right.

Each alternative now gets its own extraction, guarded by its own condition and
chained as if/else-if, so exactly one runs — the one that matched.

## Coverage

Actual VALUES are asserted for every alternative, not merely that the arm was
selected: selection was never broken, only the slot the binding was read from.
`Slice(7)` is the discriminating case; `Ptr` and `Ref` are controls that were
green on the buggy lane, so a red control means the harness, not the defect.
The same-arity grouping is the workaround that was correct before the fix and
must stay correct after it.

## Scenarios

### or-pattern with mixed-arity alternatives

#### binds the arity-1 alternative from its own slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### binds the first arity-2 alternative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(mixed(K.Ptr(5, 9)), 5)
```

</details>

#### binds the second arity-2 alternative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(mixed(K.Ref(4, 8)), 4)
```

</details>

#### still reaches the payload-free arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(mixed(K.Plain), -1)
```

</details>

#### keeps the same-arity grouped control correct for Slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(grouped(K.Slice(7)), 7)
```

</details>

#### keeps the same-arity grouped control correct for Ptr

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(grouped(K.Ptr(5, 9)), 5)
```

</details>

#### keeps the same-arity grouped control correct for Ref

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(grouped(K.Ref(4, 8)), 4)
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

- Canonical SPipe generation for source `1465dde9081f35a6b2751a578e8386c60acea06271e2a5e6408b18b535c9d35e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1465dde9081f35a6b2751a578e8386c60acea06271e2a5e6408b18b535c9d35e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1465dde9081f35a6b2751a578e8386c60acea06271e2a5e6408b18b535c9d35e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/or_pattern_mixed_arity_binding_spec.spl
mirror: doc/06_spec/01_unit/compiler/or_pattern_mixed_arity_binding_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/or_pattern_mixed_arity_binding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/or_pattern_mixed_arity_binding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/or_pattern_mixed_arity_binding_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/or_pattern_mixed_arity_binding_spec.spl:69:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'binds the arity-1 alternative from its own slot' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/or_pattern_mixed_arity_binding_spec.spl:74:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'binds the first arity-2 alternative' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/or_pattern_mixed_arity_binding_spec.spl:77:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'binds the second arity-2 alternative' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/or_pattern_mixed_arity_binding_spec.spl:80:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'still reaches the payload-free arm' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
