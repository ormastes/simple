# Type Inference Specification

> Tests covering Type Representation, Type Unification, Dependency Resolution, TypeChecker Integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Inference Specification

## Scenarios

### Type Representation

#### renders primitive and compound types

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders primitive and compound types


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders primitive and compound types")
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

- identifies primitive types


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies primitive types")
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

- unifies identical primitive types
   - Expected: msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unifies identical primitive types")
val unifier = TypeUnifier.new()
match unifier.unify(Type.Int, Type.Int):
    case Ok(()):
        check(true)
    case Err(msg):
        expect(msg).to_equal("")
```

</details>

#### rejects different primitive types

- rejects different primitive types


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects different primitive types")
val unifier = TypeUnifier.new()
match unifier.unify(Type.Int, Type.Bool):
    case Ok(()):
        check(false)
    case Err(msg):
        check(msg == "Cannot unify Int with Bool")
```

</details>

#### unifies variables and resolves chains

- unifies variables and resolves chains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unifies variables and resolves chains")
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

- detects occurs check failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects occurs check failures")
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

- unifies function, generic, tuple, array, and optional types


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unifies function, generic, tuple, array, and optional types")
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

- rejects dyn trait mismatches


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects dyn trait mismatches")
val unifier = TypeUnifier.new()
check(unifier.unify(Type.DynTrait("Read"), Type.DynTrait("Write")).is_err())
check(unifier.unify(Type.DynTrait("Read"), Type.Int).is_err())
check(unifier.unify(Type.Int, Type.DynTrait("Read")).is_err())
```

</details>

### Dependency Resolution

#### resolves transitive dependencies and deduplicates diamonds

- resolves transitive dependencies and deduplicates diamonds


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves transitive dependencies and deduplicates diamonds")
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

- skips missing dependencies without breaking resolution


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips missing dependencies without breaking resolution")
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

- collects fields without duplicates


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects fields without duplicates")
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

- creates fresh variables and binds trait interfaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates fresh variables and binds trait interfaces")
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

- tracks trait implementations for dyn trait coercion


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks trait implementations for dyn trait coercion")
val checker = TypeChecker.new()
checker.register_trait_impl("Display", Type.Int)
checker.register_trait_impl("Display", Type.Bool)
check(checker.can_coerce_to_dyn_trait(Type.Int, "Display"))
check(checker.can_coerce_to_dyn_trait(Type.Bool, "Display"))
check(not checker.can_coerce_to_dyn_trait(Type.Str, "Display"))
```

</details>

#### resolves transitive dependencies through the checker

- resolves transitive dependencies through the checker


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves transitive dependencies through the checker")
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
| Source | `test/unit/lib/std/type_checker/type_inference_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Type Representation, Type Unification, Dependency Resolution, TypeChecker Integration.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7528bde6db19d8f85e73ecfc62f6afb4e03876fe35b5daaf352fb6c718616156`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7528bde6db19d8f85e73ecfc62f6afb4e03876fe35b5daaf352fb6c718616156`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7528bde6db19d8f85e73ecfc62f6afb4e03876fe35b5daaf352fb6c718616156`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/std/type_checker/type_inference_spec.spl
mirror: doc/06_spec/unit/lib/std/type_checker/type_inference_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/type_checker/type_inference_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/type_checker/type_inference_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/type_checker/type_inference_spec.spl:521:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders primitive and compound types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/type_checker/type_inference_spec.spl:537:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identifies primitive types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/type_checker/type_inference_spec.spl:548:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unifies identical primitive types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
