# hm type inference
*Source:* `test/feature/usage/hm_type_inference_spec.spl`

## Feature: HM Type Inference Core

### Scenario: Fresh Type Variables

| # | Example | Status |
|---|---------|--------|
| 1 | creates unique type variable IDs | pass |
| 2 | creates type variables with levels | pass |

**Example:** creates unique type variable IDs
    Given val v1 = fresh_var()
    Given val v2 = fresh_var()
    Given val v3 = fresh_var()

**Example:** creates type variables with levels
    Given val t1 = ty_var(0)
    Given val t2 = ty_var(1)

### Scenario: Unification

| # | Example | Status |
|---|---------|--------|
| 1 | unifies same primitive types | pass |
| 2 | fails to unify different primitive types | pass |
| 3 | unifies type variable with concrete type | pass |
| 4 | unifies two type variables | pass |
| 5 | detects occurs check violation | pass |
| 6 | unifies function types | pass |
| 7 | unifies function types with variables | pass |

**Example:** unifies type variable with concrete type
    Given val v = ty_var(0)
    Given val resolved = subst_apply(s, v)

**Example:** unifies two type variables
    Given val v1 = ty_var(0)
    Given val v2 = ty_var(0)
    Given val r1 = subst_apply(s2, v1)
    Given val r2 = subst_apply(s2, v2)

**Example:** detects occurs check violation
    Given val v = ty_var(0)
    Given val fn_of_v = ty_fn(v, ty_int())  # v -> int

**Example:** unifies function types
    Given val f1 = ty_fn(ty_int(), ty_bool())
    Given val f2 = ty_fn(ty_int(), ty_bool())

**Example:** unifies function types with variables
    Given val v = ty_var(0)
    Given val f1 = ty_fn(v, ty_bool())        # a -> bool
    Given val f2 = ty_fn(ty_int(), ty_bool()) # int -> bool
    Given val resolved = subst_apply(s, v)

### Scenario: Level-Based Generalization

| # | Example | Status |
|---|---------|--------|
| 1 | identifies variables at higher level as generalizable | pass |
| 2 | does not generalize variables at same level | pass |
| 3 | generalizes only higher-level vars in mixed type | pass |

**Example:** identifies variables at higher level as generalizable
    Given val v = ty_var(1)  # Created at level 1
    Given val fn_ty = ty_fn(v, v)  # a -> a at level 1
    Given val free_vars = collect_free_vars(fn_ty, 0)

**Example:** does not generalize variables at same level
    Given val v = ty_var(0)
    Given val fn_ty = ty_fn(v, v)
    Given val free_vars = collect_free_vars(fn_ty, 0)

**Example:** generalizes only higher-level vars in mixed type
    Given val v0 = ty_var(0)  # At level 0 (bound in env)
    Given val v1 = ty_var(1)  # At level 1 (free)
    Given val fn_ty = ty_fn(v0, v1)  # v0 -> v1
    Given val free_vars = collect_free_vars(fn_ty, 0)

### Scenario: Let-Polymorphism Concept

| # | Example | Status |
|---|---------|--------|
| 1 | demonstrates identity can be used at multiple types | pass |

**Example:** demonstrates identity can be used at multiple types
    Given val inst1_param = ty_var(0)
    Given val inst1 = ty_fn(inst1_param, inst1_param)
    Given val use1_arg = ty_int()
    Given val resolved1 = subst_apply(s1, inst1)
    Given val inst2_param = ty_var(0)
    Given val inst2 = ty_fn(inst2_param, inst2_param)
    Given val use2_arg = ty_bool()
    Given val resolved2 = subst_apply(s2, inst2)

### Scenario: Algorithm W Core Steps

| # | Example | Status |
|---|---------|--------|
| 1 | infers identity function type | pass |
| 2 | infers application type | pass |

**Example:** infers identity function type
    Given val param_ty = ty_var(0)
    Given val return_ty = param_ty  # Body is just x
    Given val fn_ty = ty_fn(param_ty, return_ty)

**Example:** infers application type
    Given val a = ty_var(0)
    Given val b = ty_var(1)
    Given val f_ty = ty_fn(a, b)
    Given val x_ty = ty_int()
    Given val result = subst_apply(s, b)


