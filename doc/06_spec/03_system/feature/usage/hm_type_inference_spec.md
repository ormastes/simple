# Hindley-Milner Type Inference

> Tests core Hindley-Milner type inference with level-based generalization. Implements simplified type variables, substitution, and unification with occurs check to verify polymorphic functions, let-polymorphism with independent instantiations, function type unification, and Algorithm W core steps for identity and application type inference.

<!-- sdn-diagram:id=hm_type_inference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hm_type_inference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hm_type_inference_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hm_type_inference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/usage/hm_type_inference_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests core Hindley-Milner type inference with level-based generalization.
Implements simplified type variables, substitution, and unification with occurs
check to verify polymorphic functions, let-polymorphism with independent
instantiations, function type unification, and Algorithm W core steps for
identity and application type inference.

## Syntax

```simple
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

1. reset vars

2. check

3. check

4. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. reset vars

2. check

3. check

4. check

5. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check

2. check

3. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(unify_ok(ty_int(), ty_int()), "int=int should unify")
check(unify_ok(ty_bool(), ty_bool()), "bool=bool should unify")
check(unify_ok(ty_str(), ty_str()), "str=str should unify")
```

</details>

#### fails to unify different primitive types

1. check

2. check

3. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(unify_err(ty_int(), ty_bool()), "int != bool should fail")
check(unify_err(ty_str(), ty_int()), "str != int should fail")
check(unify_err(ty_bool(), ty_str()), "bool != str should fail")
```

</details>

#### unifies type variable with concrete type

1. reset vars

2. check

3. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_vars()
val v = ty_var(0)

match unify(empty_subst(), v, ty_int()):
    case Ok(s):
        val resolved = subst_apply(s, v)
        var resolved_is_int = false
        match resolved:
            case TyInt: resolved_is_int = true
            case _: resolved_is_int = false
        check(resolved_is_int, "expected int")
    case Err(_):
        check(false, "unification should succeed")
```

</details>

#### unifies two type variables

1. reset vars

2. check

3. check

4. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
                var both_int = false
                match (r1, r2):
                    case (TyInt, TyInt): both_int = true
                    case _: both_int = false
                check(both_int, "both should be int")
            case Err(_):
                check(false, "second unification failed")
    case Err(_):
        check(false, "first unification failed")
```

</details>

#### detects occurs check violation

1. reset vars


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_vars()
val v = ty_var(0)
val fn_of_v = ty_fn(v, ty_int())  # v -> int

# Try to unify v = v -> int (would create infinite type)
val r = unify(empty_subst(), v, fn_of_v)
match r:
    case Ok(_): check(false, "should fail occurs check")
    case Err(_): check(true, "occurs check failed as expected")
```

</details>

#### unifies function types

1. reset vars


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_vars()
val f1 = ty_fn(ty_int(), ty_bool())
val f2 = ty_fn(ty_int(), ty_bool())

val r = unify(empty_subst(), f1, f2)
match r:
    case Ok(_): check(true, "same function types unified")
    case Err(_): check(false, "same function types should unify")
```

</details>

#### unifies function types with variables

1. reset vars

2. check

3. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_vars()
val v = ty_var(0)
val f1 = ty_fn(v, ty_bool())        # a -> bool
val f2 = ty_fn(ty_int(), ty_bool()) # int -> bool

match unify(empty_subst(), f1, f2):
    case Ok(s):
        val resolved = subst_apply(s, v)
        var resolved_is_int = false
        match resolved:
            case TyInt: resolved_is_int = true
            case _: resolved_is_int = false
        check(resolved_is_int, "v should be int")
    case Err(_):
        check(false, "unification should succeed")
```

</details>

#### Level-Based Generalization

#### identifies variables at higher level as generalizable

1. reset vars

2. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. reset vars

2. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. reset vars

2. check

3. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. reset vars

2. check

3. check

4. reset vars

5. check

6. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
        var int_to_int = false
        match (p1, r1):
            case (TyInt, TyInt): int_to_int = true
            case _: int_to_int = false
        check(int_to_int, "expected int -> int")
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
        var bool_to_bool = false
        match (p2, r2):
            case (TyBool, TyBool): bool_to_bool = true
            case _: bool_to_bool = false
        check(bool_to_bool, "expected bool -> bool")
    case Err(_):
        check(false, "second use unification failed")
```

</details>

#### Algorithm W Core Steps

#### infers identity function type

1. reset vars

2. check

3. check

4. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. reset vars

2. var result = subst apply

3. check

4. check


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
