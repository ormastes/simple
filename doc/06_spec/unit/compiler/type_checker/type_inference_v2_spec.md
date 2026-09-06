# Type Inference V2 Specification

> Tests covering Type Inference — type variables, Type Inference — substitution store, Type Inference — substitution resolution, Type Inference — occurs check, Type Inference — unification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Inference V2 Specification

## Scenarios

### Type Inference — type variables

#### generates distinct fresh variables

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates distinct fresh variables
   - Expected: a == b is false
   - Expected: b == c is false
   - Expected: a == c is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates distinct fresh variables")
type_var_reset()
val a = type_var_fresh()
val b = type_var_fresh()
val c = type_var_fresh()
expect(a == b).to_equal(false)
expect(b == c).to_equal(false)
expect(a == c).to_equal(false)
```

</details>

#### allocates fresh variables in increasing order

- allocates fresh variables in increasing order
   - Expected: b > a is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates fresh variables in increasing order")
type_var_reset()
val a = type_var_fresh()
val b = type_var_fresh()
expect(b > a).to_equal(true)
```

</details>

#### restarts numbering after reset

- restarts numbering after reset
   - Expected: again equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restarts numbering after reset")
type_var_reset()
val first = type_var_fresh()
type_var_reset()
val again = type_var_fresh()
expect(again).to_equal(first)
```

</details>

#### classifies type variables apart from concrete types

- classifies type variables apart from concrete types
   - Expected: is_type_var(v) is true
   - Expected: is_type_var(TYPE_I64) is false
   - Expected: is_type_var(TYPE_BOOL) is false
   - Expected: is_type_var(TYPE_F64) is false
   - Expected: is_type_var(TYPE_TEXT) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies type variables apart from concrete types")
type_var_reset()
val v = type_var_fresh()
expect(is_type_var(v)).to_equal(true)
expect(is_type_var(TYPE_I64)).to_equal(false)
expect(is_type_var(TYPE_BOOL)).to_equal(false)
expect(is_type_var(TYPE_F64)).to_equal(false)
expect(is_type_var(TYPE_TEXT)).to_equal(false)
```

</details>

### Type Inference — substitution store

#### reports an unbound variable as unbound

- reports an unbound variable as unbound
   - Expected: unify_is_bound(v) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an unbound variable as unbound")
type_var_reset()
unify_reset()
val v = type_var_fresh()
expect(unify_is_bound(v)).to_equal(false)
```

</details>

#### binds a variable to a concrete type and looks it up

- binds a variable to a concrete type and looks it up
   - Expected: unify_is_bound(v) is true
   - Expected: unify_lookup(v) equals `TYPE_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds a variable to a concrete type and looks it up")
type_var_reset()
unify_reset()
val v = type_var_fresh()
unify_bind(v, TYPE_I64)
expect(unify_is_bound(v)).to_equal(true)
expect(unify_lookup(v)).to_equal(TYPE_I64)
```

</details>

#### keeps separate bindings for separate variables

- keeps separate bindings for separate variables
   - Expected: unify_lookup(v1) equals `TYPE_I64`
   - Expected: unify_lookup(v2) equals `TYPE_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps separate bindings for separate variables")
type_var_reset()
unify_reset()
val v1 = type_var_fresh()
val v2 = type_var_fresh()
unify_bind(v1, TYPE_I64)
unify_bind(v2, TYPE_TEXT)
expect(unify_lookup(v1)).to_equal(TYPE_I64)
expect(unify_lookup(v2)).to_equal(TYPE_TEXT)
```

</details>

#### returns -1 when looking up an unbound variable

- returns -1 when looking up an unbound variable
   - Expected: unify_lookup(v) equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 when looking up an unbound variable")
type_var_reset()
unify_reset()
val v = type_var_fresh()
expect(unify_lookup(v)).to_equal(0 - 1)
```

</details>

#### clears every binding on reset

- clears every binding on reset
   - Expected: unify_is_bound(v) is true
   - Expected: unify_is_bound(v) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears every binding on reset")
type_var_reset()
unify_reset()
val v = type_var_fresh()
unify_bind(v, TYPE_I64)
expect(unify_is_bound(v)).to_equal(true)
unify_reset()
expect(unify_is_bound(v)).to_equal(false)
```

</details>

### Type Inference — substitution resolution

#### leaves a concrete type unchanged

- leaves a concrete type unchanged
   - Expected: type_subst_apply(TYPE_I64) equals `TYPE_I64`
   - Expected: type_subst_apply(TYPE_TEXT) equals `TYPE_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves a concrete type unchanged")
unify_reset()
expect(type_subst_apply(TYPE_I64)).to_equal(TYPE_I64)
expect(type_subst_apply(TYPE_TEXT)).to_equal(TYPE_TEXT)
```

</details>

#### leaves an unbound variable unchanged

- leaves an unbound variable unchanged
   - Expected: type_subst_apply(v) equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves an unbound variable unchanged")
type_var_reset()
unify_reset()
val v = type_var_fresh()
expect(type_subst_apply(v)).to_equal(v)
```

</details>

#### resolves a single binding

- resolves a single binding
   - Expected: type_subst_apply(v) equals `TYPE_F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a single binding")
type_var_reset()
unify_reset()
val v = type_var_fresh()
unify_bind(v, TYPE_F64)
expect(type_subst_apply(v)).to_equal(TYPE_F64)
```

</details>

#### follows a transitive chain to the concrete type

- follows a transitive chain to the concrete type
   - Expected: type_subst_apply(v1) equals `TYPE_BOOL`
   - Expected: type_subst_apply(v2) equals `TYPE_BOOL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("follows a transitive chain to the concrete type")
type_var_reset()
unify_reset()
val v1 = type_var_fresh()
val v2 = type_var_fresh()
val v3 = type_var_fresh()
unify_bind(v1, v2)
unify_bind(v2, v3)
unify_bind(v3, TYPE_BOOL)
expect(type_subst_apply(v1)).to_equal(TYPE_BOOL)
expect(type_subst_apply(v2)).to_equal(TYPE_BOOL)
```

</details>

#### stops at the last unbound variable in a chain

- stops at the last unbound variable in a chain
   - Expected: type_subst_apply(v1) equals `v2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops at the last unbound variable in a chain")
type_var_reset()
unify_reset()
val v1 = type_var_fresh()
val v2 = type_var_fresh()
unify_bind(v1, v2)
expect(type_subst_apply(v1)).to_equal(v2)
```

</details>

### Type Inference — occurs check

#### reports no occurrence for an unrelated concrete type

- reports no occurrence for an unrelated concrete type
   - Expected: occurs_check(v, TYPE_I64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no occurrence for an unrelated concrete type")
type_var_reset()
unify_reset()
val v = type_var_fresh()
expect(occurs_check(v, TYPE_I64)).to_equal(false)
```

</details>

#### reports an occurrence when the variable is itself

- reports an occurrence when the variable is itself
   - Expected: occurs_check(v, v) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an occurrence when the variable is itself")
type_var_reset()
unify_reset()
val v = type_var_fresh()
expect(occurs_check(v, v)).to_equal(true)
```

</details>

#### reports an occurrence through a substitution chain

- reports an occurrence through a substitution chain
   - Expected: occurs_check(v1, v2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an occurrence through a substitution chain")
type_var_reset()
unify_reset()
val v1 = type_var_fresh()
val v2 = type_var_fresh()
unify_bind(v2, v1)
expect(occurs_check(v1, v2)).to_equal(true)
```

</details>

#### reports no occurrence for a different unbound variable

- reports no occurrence for a different unbound variable
   - Expected: occurs_check(v1, v2) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no occurrence for a different unbound variable")
type_var_reset()
unify_reset()
val v1 = type_var_fresh()
val v2 = type_var_fresh()
expect(occurs_check(v1, v2)).to_equal(false)
```

</details>

### Type Inference — unification

#### succeeds on two identical primitives

- succeeds on two identical primitives
   - Expected: unify_types(TYPE_I64, TYPE_I64) equals `UNIFY_SUCCESS`
   - Expected: unify_types(TYPE_BOOL, TYPE_BOOL) equals `UNIFY_SUCCESS`
   - Expected: unify_types(TYPE_TEXT, TYPE_TEXT) equals `UNIFY_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("succeeds on two identical primitives")
unify_reset()
expect(unify_types(TYPE_I64, TYPE_I64)).to_equal(UNIFY_SUCCESS)
expect(unify_types(TYPE_BOOL, TYPE_BOOL)).to_equal(UNIFY_SUCCESS)
expect(unify_types(TYPE_TEXT, TYPE_TEXT)).to_equal(UNIFY_SUCCESS)
```

</details>

#### fails with a mismatch on two different primitives

- fails with a mismatch on two different primitives
   - Expected: unify_types(TYPE_I64, TYPE_TEXT) equals `UNIFY_FAIL_MISMATCH`
   - Expected: unify_types(TYPE_BOOL, TYPE_F64) equals `UNIFY_FAIL_MISMATCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails with a mismatch on two different primitives")
unify_reset()
expect(unify_types(TYPE_I64, TYPE_TEXT)).to_equal(UNIFY_FAIL_MISMATCH)
expect(unify_types(TYPE_BOOL, TYPE_F64)).to_equal(UNIFY_FAIL_MISMATCH)
```

</details>

#### binds a variable on the left to a concrete type

- binds a variable on the left to a concrete type
   - Expected: unify_types(v, TYPE_I64) equals `UNIFY_SUCCESS`
   - Expected: type_subst_apply(v) equals `TYPE_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds a variable on the left to a concrete type")
type_var_reset()
unify_reset()
val v = type_var_fresh()
expect(unify_types(v, TYPE_I64)).to_equal(UNIFY_SUCCESS)
expect(type_subst_apply(v)).to_equal(TYPE_I64)
```

</details>

#### binds a variable on the right to a concrete type

- binds a variable on the right to a concrete type
   - Expected: unify_types(TYPE_TEXT, v) equals `UNIFY_SUCCESS`
   - Expected: type_subst_apply(v) equals `TYPE_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds a variable on the right to a concrete type")
type_var_reset()
unify_reset()
val v = type_var_fresh()
expect(unify_types(TYPE_TEXT, v)).to_equal(UNIFY_SUCCESS)
expect(type_subst_apply(v)).to_equal(TYPE_TEXT)
```

</details>

#### unifies two variables so they resolve together

- unifies two variables so they resolve together
   - Expected: unify_types(v1, v2) equals `UNIFY_SUCCESS`
   - Expected: unify_types(v2, TYPE_BOOL) equals `UNIFY_SUCCESS`
   - Expected: type_subst_apply(v1) equals `TYPE_BOOL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unifies two variables so they resolve together")
type_var_reset()
unify_reset()
val v1 = type_var_fresh()
val v2 = type_var_fresh()
expect(unify_types(v1, v2)).to_equal(UNIFY_SUCCESS)
expect(unify_types(v2, TYPE_BOOL)).to_equal(UNIFY_SUCCESS)
expect(type_subst_apply(v1)).to_equal(TYPE_BOOL)
```

</details>

#### is reflexive on a type variable

- is reflexive on a type variable
   - Expected: unify_types(v, v) equals `UNIFY_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is reflexive on a type variable")
type_var_reset()
unify_reset()
val v = type_var_fresh()
expect(unify_types(v, v)).to_equal(UNIFY_SUCCESS)
```

</details>

#### succeeds when both sides resolve to the same variable

- succeeds when both sides resolve to the same variable
   - Expected: unify_types(v1, v2) equals `UNIFY_SUCCESS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("succeeds when both sides resolve to the same variable")
type_var_reset()
unify_reset()
val v1 = type_var_fresh()
val v2 = type_var_fresh()
unify_bind(v2, v1)
expect(unify_types(v1, v2)).to_equal(UNIFY_SUCCESS)
```

</details>

#### records a message on mismatch

- records a message on mismatch
   - Expected: unify_types(TYPE_I64, TYPE_TEXT) equals `UNIFY_FAIL_MISMATCH`
   - Expected: unify_get_error() equals `Type mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a message on mismatch")
unify_reset()
expect(unify_types(TYPE_I64, TYPE_TEXT)).to_equal(UNIFY_FAIL_MISMATCH)
expect(unify_get_error()).to_equal("Type mismatch")
```

</details>

#### keeps the three status codes distinct

- keeps the three status codes distinct
   - Expected: UNIFY_SUCCESS == UNIFY_FAIL_MISMATCH is false
   - Expected: UNIFY_SUCCESS == UNIFY_FAIL_OCCURS is false
   - Expected: UNIFY_FAIL_MISMATCH == UNIFY_FAIL_OCCURS is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the three status codes distinct")
expect(UNIFY_SUCCESS == UNIFY_FAIL_MISMATCH).to_equal(false)
expect(UNIFY_SUCCESS == UNIFY_FAIL_OCCURS).to_equal(false)
expect(UNIFY_FAIL_MISMATCH == UNIFY_FAIL_OCCURS).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/type_checker/type_inference_v2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Type Inference — type variables, Type Inference — substitution store, Type Inference — substitution resolution, Type Inference — occurs check, Type Inference — unification.
- Type Inference — type variables
- Type Inference — substitution store
- Type Inference — substitution resolution
- Type Inference — occurs check
- Type Inference — unification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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

- Canonical SPipe generation for source `3822a931ed25bd483ee1945aac9923a8ef47e9b085e6731b134bd3fe4d4efb19`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3822a931ed25bd483ee1945aac9923a8ef47e9b085e6731b134bd3fe4d4efb19`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3822a931ed25bd483ee1945aac9923a8ef47e9b085e6731b134bd3fe4d4efb19`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/type_checker/type_inference_v2_spec.spl
mirror: doc/06_spec/unit/compiler/type_checker/type_inference_v2_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/type_checker/type_inference_v2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/type_checker/type_inference_v2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/type_checker/type_inference_v2_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates distinct fresh variables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/type_checker/type_inference_v2_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates fresh variables in increasing order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/type_checker/type_inference_v2_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'restarts numbering after reset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
