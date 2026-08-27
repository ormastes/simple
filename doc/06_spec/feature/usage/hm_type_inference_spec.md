# Hindley-Milner Type Inference

> Tests core Hindley-Milner type inference with level-based generalization. Implements simplified type variables, substitution, and unification with occurs check to verify polymorphic functions, let-polymorphism with independent instantiations, function type unification, and Algorithm W core steps for identity and application type inference.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hindley-Milner Type Inference

Tests core Hindley-Milner type inference with level-based generalization. Implements simplified type variables, substitution, and unification with occurs check to verify polymorphic functions, let-polymorphism with independent instantiations, function type unification, and Algorithm W core steps for identity and application type inference.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TYPE-001 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/feature/usage/hm_type_inference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests core Hindley-Milner type inference with level-based generalization.
Implements simplified type variables, substitution, and unification with occurs
check to verify polymorphic functions, let-polymorphism with independent
instantiations, function type unification, and Algorithm W core steps for
identity and application type inference.

## Syntax

```simple
use std.spec.step

val v = ty_var(0)
val fn_ty = ty_fn(v, v)  # a -> a
var result = unify(empty_subst(), v, ty_int())
val free_vars = collect_free_vars(fn_ty, 0)
```
HM Type Inference Specification

Tests for Hindley-Milner type inference with level-based generalization.
Verifies that the type inference correctly handles:
- Polymorphic functions (identity, compose)
- Let-polymorphism (multiple instantiations)
- Unification with occurs check
- Level-based generalization

Feature: #2500 - HM Type Inference
Status: in_progress

NOTE: Full tests require self-hosting compiler modules (simple/compiler/*).
      These simplified tests verify core concepts using built-in primitives.

## Scenarios

### HM Type Inference Core

#### Fresh Type Variables

#### creates unique type variable IDs

- creates unique type variable IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates unique type variable IDs")
reset_vars()
val v1 = fresh_var()
val v2 = fresh_var()
val v3 = fresh_var()

check(v1 == 0, "first var should be 0")
check(v2 == 1, "second var should be 1")
check(v3 == 2, "third var should be 2")
```

</details>

#### creates type variables with levels

- creates type variables with levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates type variables with levels")
reset_vars()
val t1 = ty_var(0)
val t2 = ty_var(1)

check(is_var(t1), "t1 should be var")
check(is_var(t2), "t2 should be var")
check(get_var_level(t1) == 0, "t1 at level 0")
check(get_var_level(t2) == 1, "t2 at level 1")
```

</details>

#### Unification

#### unifies same primitive types

- unifies same primitive types


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unifies same primitive types")
# Direct test with match on result
val r_int = unify(empty_subst(), ty_int(), ty_int())
match r_int:
    case Ok(_): pass
    case Err(_): assert false, "int=int failed"
val r_bool = unify(empty_subst(), ty_bool(), ty_bool())
match r_bool:
    case Ok(_): pass
    case Err(_): assert false, "bool=bool failed"
val r_str = unify(empty_subst(), ty_str(), ty_str())
match r_str:
    case Ok(_): pass
    case Err(_): assert false, "str=str failed"
```

</details>

#### fails to unify different primitive types

- fails to unify different primitive types


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fails to unify different primitive types")
val r1 = unify(empty_subst(), ty_int(), ty_bool())
match r1:
    case Ok(_): assert false, "int != bool should fail"
    case Err(_): pass
val r2 = unify(empty_subst(), ty_str(), ty_int())
match r2:
    case Ok(_): assert false, "str != int should fail"
    case Err(_): pass
val r3 = unify(empty_subst(), ty_bool(), ty_str())
match r3:
    case Ok(_): assert false, "bool != str should fail"
    case Err(_): pass
```

</details>

#### unifies type variable with concrete type

- unifies type variable with concrete type


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unifies type variable with concrete type")
reset_vars()
val v = ty_var(0)

match unify(empty_subst(), v, ty_int()):
    case Ok(s):
        val resolved = subst_apply(s, v)
        match resolved:
            case TyInt: assert true
            case _: assert false, "expected int"
    case Err(_):
        check(false, "unification should succeed")
```

</details>

#### unifies two type variables

- unifies two type variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unifies two type variables")
reset_vars()
val v1 = ty_var(0)
val v2 = ty_var(0)

# Unify v1 with v2
match unify(empty_subst(), v1, v2):
    case Ok(s1):
        # Then unify v1 with int
        match unify(s1, v1, ty_int()):
            case Ok(s2):
                # Both should resolve to int
                val r1 = subst_apply(s2, v1)
                val r2 = subst_apply(s2, v2)
                match (r1, r2):
                    case (TyInt, TyInt): assert true
                    case _: assert false, "both should be int"
            case Err(_):
                check(false, "second unification failed")
    case Err(_):
        check(false, "first unification failed")
```

</details>

#### detects occurs check violation

- detects occurs check violation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects occurs check violation")
reset_vars()
val v = ty_var(0)
val fn_of_v = ty_fn(v, ty_int())  # v -> int

# Try to unify v = v -> int (would create infinite type)
val r = unify(empty_subst(), v, fn_of_v)
match r:
    case Ok(_): assert false, "should fail occurs check"
    case Err(_): pass
```

</details>

#### unifies function types

- unifies function types


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unifies function types")
reset_vars()
val f1 = ty_fn(ty_int(), ty_bool())
val f2 = ty_fn(ty_int(), ty_bool())

val r = unify(empty_subst(), f1, f2)
match r:
    case Ok(_): pass
    case Err(_): assert false, "same function types should unify"
```

</details>

#### unifies function types with variables

- unifies function types with variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unifies function types with variables")
reset_vars()
val v = ty_var(0)
val f1 = ty_fn(v, ty_bool())        # a -> bool
val f2 = ty_fn(ty_int(), ty_bool()) # int -> bool

match unify(empty_subst(), f1, f2):
    case Ok(s):
        val resolved = subst_apply(s, v)
        match resolved:
            case TyInt: assert true
            case _: assert false, "v should be int"
    case Err(_):
        check(false, "unification should succeed")
```

</details>

#### Level-Based Generalization

#### identifies variables at higher level as generalizable

- identifies variables at higher level as generalizable


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("identifies variables at higher level as generalizable")
reset_vars()
# Simulate entering a let-binding (level 1)
val v = ty_var(1)  # Created at level 1
val fn_ty = ty_fn(v, v)  # a -> a at level 1

# At level 0, variables at level 1 are generalizable
val free_vars = collect_free_vars(fn_ty, 0)
check(free_vars.len() == 1, "should have one generalizable var")
```

</details>

#### does not generalize variables at same level

- does not generalize variables at same level


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not generalize variables at same level")
reset_vars()
# Variable created at level 0
val v = ty_var(0)
val fn_ty = ty_fn(v, v)

# At level 0, variables at level 0 are NOT generalizable
val free_vars = collect_free_vars(fn_ty, 0)
check(free_vars.len() == 0, "should have no generalizable vars")
```

</details>

#### generalizes only higher-level vars in mixed type

- generalizes only higher-level vars in mixed type


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("generalizes only higher-level vars in mixed type")
reset_vars()
val v0 = ty_var(0)  # At level 0 (bound in env)
val v1 = ty_var(1)  # At level 1 (free)
val fn_ty = ty_fn(v0, v1)  # v0 -> v1

# At level 0, only v1 is generalizable
val free_vars = collect_free_vars(fn_ty, 0)
check(free_vars[0] == get_var_id(v1), "v1 should be generalizable")
check(free_vars.len() == 1, "should have one generalizable var")
```

</details>

#### Let-Polymorphism Concept

#### demonstrates identity can be used at multiple types

- demonstrates identity can be used at multiple types


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("demonstrates identity can be used at multiple types")
# Simulates: let id = \x: x in (id 1, id true)
# The key insight: after generalizing id's type (forall a. a -> a),
# each use gets fresh instantiation

reset_vars()

# First use: id(1) - instantiate with fresh var, unify with int
val inst1_param = ty_var(0)
val inst1 = ty_fn(inst1_param, inst1_param)
val use1_arg = ty_int()

match unify(empty_subst(), inst1_param, use1_arg):
    case Ok(s1):
        val resolved1 = subst_apply(s1, inst1)
        # inst1 should be int -> int
        val p1 = get_fn_param(resolved1)
        val r1 = get_fn_ret(resolved1)
        match (p1, r1):
            case (TyInt, TyInt): assert true
            case _: assert false, "expected int -> int"
    case Err(_):
        check(false, "first use unification failed")

# Second use: id(true) - NEW fresh var (independent instantiation)
reset_vars()  # Reset to simulate fresh instantiation
val inst2_param = ty_var(0)
val inst2 = ty_fn(inst2_param, inst2_param)
val use2_arg = ty_bool()

match unify(empty_subst(), inst2_param, use2_arg):
    case Ok(s2):
        val resolved2 = subst_apply(s2, inst2)
        # inst2 should be bool -> bool
        val p2 = get_fn_param(resolved2)
        val r2 = get_fn_ret(resolved2)
        match (p2, r2):
            case (TyBool, TyBool): assert true
            case _: assert false, "expected bool -> bool"
    case Err(_):
        check(false, "second use unification failed")
```

</details>

#### Algorithm W Core Steps

#### infers identity function type

- infers identity function type


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("infers identity function type")
# Simulate: fn identity(x): x
# 1. Create fresh var for param: a
# 2. Return type = param type (since body is just x)
# 3. Function type = a -> a
reset_vars()
val param_ty = ty_var(0)
val return_ty = param_ty  # Body is just x
val fn_ty = ty_fn(param_ty, return_ty)

check(is_var(param_ty), "param is variable")
match fn_ty:
    case TyFn(data):
        check(get_var_id(data.param) == get_var_id(data.ret_type), "param and return same var")
    case _:
        check(false, "expected function type")
```

</details>

#### infers application type

- infers application type


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("infers application type")
# Simulate: f(x) where f: a -> b, x: a
# Result type should be b
reset_vars()
val a = ty_var(0)
val b = ty_var(1)
val f_ty = ty_fn(a, b)
val x_ty = ty_int()

# Unify param with arg
match unify(empty_subst(), a, x_ty):
    case Ok(s):
        # Result is b with substitution applied
        var result = subst_apply(s, b)
        # b is still a variable (no constraint on return)
        check(is_var(result), "result is still variable")
    case Err(_):
        check(false, "unification failed")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58200e86681005569ac2f42b6f848e38679734b52a236b08da36e05f798bafbf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58200e86681005569ac2f42b6f848e38679734b52a236b08da36e05f798bafbf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58200e86681005569ac2f42b6f848e38679734b52a236b08da36e05f798bafbf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/hm_type_inference_spec.spl
mirror: doc/06_spec/feature/usage/hm_type_inference_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/hm_type_inference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/hm_type_inference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/hm_type_inference_spec.spl:285:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates unique type variable IDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/hm_type_inference_spec.spl:297:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates type variables with levels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/hm_type_inference_spec.spl:310:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unifies same primitive types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
