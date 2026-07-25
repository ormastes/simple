# Dynamic Trait Objects (dyn Trait)

> Feature: Type inference for dynamic trait dispatch

<!-- sdn-diagram:id=dyn_trait_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dyn_trait_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dyn_trait_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dyn_trait_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Trait Objects (dyn Trait)

Feature: Type inference for dynamic trait dispatch

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/type_inference/dyn_trait_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: Type inference for dynamic trait dispatch
Category: Type System
Status: Executable coverage via local doubles

## Scenarios

### Dynamic Trait Objects

#### same dyn trait types unify

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
check(checker.unify(Type.dyn_trait("Display"), Type.dyn_trait("Display")))
```

</details>

#### different dyn trait types do not unify

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
check(not checker.unify(Type.dyn_trait("Display"), Type.dyn_trait("Debug")))
```

</details>

#### concrete type coerces to dyn Trait

1. checker register trait impl
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
checker.register_trait_impl("Display")
check(checker.can_coerce_to_dyn_trait("Person", "Display"))
```

</details>

#### dyn Trait in array types

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
check(checker.unify(Type.array("dyn Display"), Type.array("dyn Display")))
```

</details>

#### dyn Trait in Optional types

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
check(checker.unify(Type.optional("dyn Display"), Type.optional("dyn Display")))
```

</details>

#### static dispatch with interface binding

1. checker bind interface
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
checker.bind_interface("Display")
check(checker.dispatch_mode("Display") == DispatchMode.Static)
```

</details>

#### dynamic dispatch without interface binding

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
check(checker.dispatch_mode("Display") == DispatchMode.Dynamic)
```

</details>

#### cannot assign dyn Trait to concrete type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
check(not checker.unify(Type.dyn_trait("Display"), Type.concrete("Person")))
```

</details>

#### dyn Trait method calls type check

1. checker bind interface
2. checker register method
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
checker.bind_interface("Display")
checker.register_method("render")
check(checker.method_call_type_checks("Display", "render"))
```

</details>

#### dyn Trait with generic methods

1. checker bind interface
2. checker register method
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checker = TypeChecker.new()
checker.bind_interface("Iterable")
checker.register_method("map")
check(checker.method_call_type_checks("Iterable", "map"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
