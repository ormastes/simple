# Type Inference Specification

> 1. check

<!-- sdn-diagram:id=type_inference_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_inference_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_inference_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_inference_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Inference Specification

## Scenarios

### Type Representation

#### renders primitive and compound types

1. check
2. check
3. check
4. check
5. check
6. check
7. check
8. check
9. check
10. check
11. check
12. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(Type.Int.to_string() == "Int")
check(Type.Bool.to_string() == "Bool")
check(Type.Str.to_string() == "Str")
check(Type.Float.to_string() == "Float")
check(Type.Unit.to_string() == "Unit")
check(Type.Var(7).to_string() == "T7")
check(Type.Function([Type.Int, Type.Bool], Type.Unit).to_string() == "fn(Int, Bool) -> Unit")
check(Type.Generic("List", [Type.Int]).to_string() == "List<Int>")
check(Type.DynTrait("Renderable").to_string() == "dyn Renderable")
check(Type.Tuple([Type.Int, Type.Bool]).to_string() == "(Int, Bool)")
check(Type.Array(Type.Str).to_string() == "[Str]")
check(Type.Optional(Type.Int).to_string() == "Option<Int>")
```

</details>

#### identifies primitive types

1. check
2. check
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(Type.Int.is_primitive())
check(Type.Bool.is_primitive())
check(Type.Str.is_primitive())
check(Type.Float.is_primitive())
check(Type.Unit.is_primitive())
check(not Type.Var(0).is_primitive())
```

</details>

### Type Unification

#### unifies identical primitive types

1. check
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unifier = TypeUnifier.new()
match unifier.unify(Type.Int, Type.Int):
    case Ok(()):
        check(true)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### rejects different primitive types

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unifier = TypeUnifier.new()
match unifier.unify(Type.Int, Type.Bool):
    case Ok(()):
        check(false)
    case Err(msg):
        check(msg == "Cannot unify Int with Bool")
```

</details>

#### unifies variables and resolves chains

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unifier = TypeUnifier.new()
val a = unifier.fresh_var()
val b = unifier.fresh_var()
check(unifier.unify(a, b).is_ok())
check(unifier.unify(b, Type.Int).is_ok())
check(type_equals(unifier.resolve(a), Type.Int))
check(type_equals(unifier.resolve(b), Type.Int))
```

</details>

#### detects occurs check failures

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unifier = TypeUnifier.new()
val a = unifier.fresh_var()
match unifier.unify(a, Type.Array(a)):
    case Ok(()):
        check(false)
    case Err(msg):
        check(msg == "Occurs check failed: infinite type")
```

</details>

#### unifies function, generic, tuple, array, and optional types

1. Type Function
2. Type Function
3. Type Function
4. Type Function
5. Type Generic
6. Type Generic
7. Type Generic
8. Type Generic
9. Type Tuple
10. Type Tuple
11. Type Tuple
12. Type Tuple
13. check
14. check
15. check
16. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unifier = TypeUnifier.new()
check(unifier.unify(
    Type.Function([Type.Int, Type.Bool], Type.Unit),
    Type.Function([Type.Int, Type.Bool], Type.Unit)
).is_ok())
check(unifier.unify(
    Type.Function([Type.Int], Type.Unit),
    Type.Function([Type.Int, Type.Bool], Type.Unit)
).is_err())
check(unifier.unify(
    Type.Generic("Map", [Type.Int, Type.Str]),
    Type.Generic("Map", [Type.Int, Type.Str])
).is_ok())
check(unifier.unify(
    Type.Generic("Map", [Type.Int]),
    Type.Generic("Set", [Type.Int])
).is_err())
check(unifier.unify(
    Type.Tuple([Type.Int, Type.Bool]),
    Type.Tuple([Type.Int, Type.Bool])
).is_ok())
check(unifier.unify(
    Type.Tuple([Type.Int]),
    Type.Tuple([Type.Int, Type.Bool])
).is_err())
check(unifier.unify(Type.Array(Type.Int), Type.Array(Type.Int)).is_ok())
check(unifier.unify(Type.Array(Type.Int), Type.Array(Type.Bool)).is_err())
check(unifier.unify(Type.Optional(Type.Str), Type.Optional(Type.Str)).is_ok())
check(unifier.unify(Type.Optional(Type.Str), Type.Optional(Type.Bool)).is_err())
```

</details>

#### rejects dyn trait mismatches

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unifier = TypeUnifier.new()
check(unifier.unify(Type.DynTrait("Read"), Type.DynTrait("Write")).is_err())
check(unifier.unify(Type.DynTrait("Read"), Type.Int).is_err())
check(unifier.unify(Type.Int, Type.DynTrait("Read")).is_err())
```

</details>

### Dependency Resolution

#### resolves transitive dependencies and deduplicates diamonds

1. resolver register dependency
2. resolver register dependency
3. resolver register dependency
4. resolver register dependency
5. check
6. check
7. check
8. check
9. check
10. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = DependencyResolver.new()

val base = DependencyInfo.new("base")
val left = DependencyInfo.new("left")
val right = DependencyInfo.new("right")
val top = DependencyInfo.new("top")

left.required_deps = ["base"]
right.required_deps = ["base"]
top.required_deps = ["left", "right"]

resolver.register_dependency(base)
resolver.register_dependency(left)
resolver.register_dependency(right)
resolver.register_dependency(top)

val resolved = resolver.resolve_transitive(["top"])
check(resolved.len() == 4)
check(contains_text(resolved, "base"))
check(contains_text(resolved, "left"))
check(contains_text(resolved, "right"))
check(contains_text(resolved, "top"))
check(resolved.len() == 4)
```

</details>

#### skips missing dependencies without breaking resolution

1. resolver register dependency
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = DependencyResolver.new()

val leaf = DependencyInfo.new("leaf")
leaf.required_deps = ["missing"]

resolver.register_dependency(leaf)

val resolved = resolver.resolve_transitive(["leaf"])
check(resolved.len() == 1)
check(contains_text(resolved, "leaf"))
```

</details>

#### collects fields without duplicates

1. base fields = [
2. extra fields = [
3. resolver register dependency
4. resolver register dependency
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = DependencyResolver.new()

val base = DependencyInfo.new("base")
base.fields = [("id", Type.Int), ("name", Type.Str)]

val extra = DependencyInfo.new("extra")
extra.fields = [("name", Type.Bool), ("active", Type.Bool)]
extra.required_deps = ["base"]

resolver.register_dependency(base)
resolver.register_dependency(extra)

val fields = resolver.collect_fields(["extra"])
check(fields.len() == 3)
check(same_pairs(fields, [("id", Type.Int), ("name", Type.Str), ("active", Type.Bool)]))
```

</details>

### TypeChecker Integration

#### creates fresh variables and binds trait interfaces

1. check
2. checker bind interface
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
val first = checker.fresh_var()
val second = checker.fresh_var()
check(not type_equals(first, second))

checker.bind_interface("Renderable", Type.Generic("Widget", []))
check(type_equals(checker.resolve_trait_type("Renderable"), Type.Generic("Widget", [])))
check(type_equals(checker.resolve_trait_type("Missing"), Type.DynTrait("Missing")))
check(checker.get_dispatch_mode("Renderable") == DispatchMode.Static)
check(checker.get_dispatch_mode("Missing") == DispatchMode.Dynamic)
```

</details>

#### tracks trait implementations for dyn trait coercion

1. checker register trait impl
2. checker register trait impl
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
checker.register_trait_impl("Display", Type.Int)
checker.register_trait_impl("Display", Type.Bool)
check(checker.can_coerce_to_dyn_trait(Type.Int, "Display"))
check(checker.can_coerce_to_dyn_trait(Type.Bool, "Display"))
check(not checker.can_coerce_to_dyn_trait(Type.Str, "Display"))
```

</details>

#### resolves transitive dependencies through the checker

1. core fields = [
2. model fields = [
3. checker register dependency
4. checker register dependency
5. check
6. check
7. check
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()

val core = DependencyInfo.new("core")
core.fields = [("id", Type.Int)]

val model = DependencyInfo.new("model")
model.fields = [("name", Type.Str)]
model.required_deps = ["core"]

checker.register_dependency(core)
checker.register_dependency(model)

val resolved = checker.resolve_transitive(["model"])
check(resolved.len() == 2)
check(contains_text(resolved, "core"))
check(contains_text(resolved, "model"))
check(same_pairs(checker.collect_fields(["model"]), [("id", Type.Int), ("name", Type.Str)]))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/type_checker/type_inference_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Type Representation
- Type Unification
- Dependency Resolution
- TypeChecker Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
