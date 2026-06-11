# Type Infer Correctness Specification

> 1. check

<!-- sdn-diagram:id=type_infer_correctness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_infer_correctness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_infer_correctness_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_infer_correctness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Infer Correctness Specification

## Scenarios

### Type inference correctness

### Basic type inference

#### infers identity function type

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ty = infer_type("fn id(x): x")
check(ty.is_ok())
check(ty.is_polymorphic())
check(ty.param_count() == 1)
check(ty.return_type_equals_param(0))
```

</details>

#### infers constant function

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ty = infer_type("fn const_five(): 5")
check(ty.is_ok())
check(ty.param_count() == 0)
check(ty.return_type().is_int())
```

</details>

#### infers addition

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ty = infer_type("fn add(x, y): x + y")
check(ty.is_ok())
check(ty.param_count() == 2)
check(ty.return_type().is_i64())
```

</details>

### Polymorphism and unification

#### generalizes let-bound functions

1. fn test
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ty = infer_type("""
fn test():
    val id = \\x: x
    val a = id(5)
    val b = id("hello")
    a
""")
check(ty.is_ok())
```

</details>

#### does not generalize mutable variables

1. fn test
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = infer_type("""
fn test():
    var x = 5
    x = "hello"
""")
check(result.is_err())
```

</details>

#### unifies generic composition

1. fn compose
2. f
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ty = infer_type("""
fn compose(f, g, x):
    f(g(x))
""")
check(ty.is_ok())
check(ty.is_polymorphic())
check(ty.type_var_count() >= 3)
```

</details>

### Data shapes

#### infers tuple and array shapes

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tuple_ty = infer_type("fn make_pair(x, y): (x, y)")
val array_ty = infer_type("fn make_array(): [1, 2, 3]")
check(tuple_ty.is_ok())
check(array_ty.is_ok())
check(array_ty.return_type().is_array())
```

</details>

#### infers option constructors

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val some_ty = infer_type("fn wrap(x): Some(x)")
val none_ty = infer_type("fn nothing(): None")
check(some_ty.is_ok())
check(none_ty.is_ok())
```

</details>

### Annotations and errors

#### respects explicit type annotations

1. fn add ints
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ty = infer_type("""
fn add_ints(x: i64, y: i64) -> i64:
    x + y
""")
check(ty.is_ok())
check(ty.param_types()[0].is_i64())
check(ty.param_types()[1].is_i64())
check(ty.return_type().is_i64())
```

</details>

#### reports clear type mismatch errors

1. fn wrong
2. check
3. check text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = infer_type("""
fn wrong(x: i64) -> text:
    x
""")
check(result.is_err())
val err = result.unwrap_err()
check_text(err, "type mismatch: i64 vs text")
```

</details>

#### detects occurs checks

1. fn omega
2. x
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = infer_type("""
fn omega(x):
    x(x)
""")
check(result.is_err())
```

</details>

### Context substitution

#### resolves substitution chains

1. ctx unify
2. ctx unify
3. ctx unify
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = HmInferContext.new()
val t1 = ctx.fresh_var()
val t2 = ctx.fresh_var()
val t3 = ctx.fresh_var()

ctx.unify(t1, t2)
ctx.unify(t2, t3)
ctx.unify(t3, HirType.i64())

val resolved = ctx.resolve(t1)
check(resolved.is_i64())
```

</details>

### Regression checks

#### handles nested and generic examples

1. fn test
2. fn inner
3. inner
4. f: fn
5. g: fn
6. h: fn
7. g
8. check
9. check
10. check
11. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = infer_type("""
fn test():
    val outer = \\x: x
    fn inner():
        val inner_var = outer(5)
        inner_var
    inner()
""")
val many = infer_type("fn many_vars(x0, x1, x2): x0")
val poly_ty = infer_type("""
fn complex<T, U, V>(
    f: fn(T) -> U,
    g: fn(U) -> V,
    h: fn(V) -> T,
    x: T
) -> V:
    g(f(x))
""")
check(nested.is_ok())
check(many.is_ok())
check(poly_ty.is_ok())
check(poly_ty.type_var_count() >= 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/type_infer/type_infer_correctness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Type inference correctness
- Basic type inference
- Polymorphism and unification
- Data shapes
- Annotations and errors
- Context substitution
- Regression checks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
