# mixin_integration_spec

> Mixin and Static Polymorphism Integration Tests.

<!-- sdn-diagram:id=mixin_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mixin_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mixin_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mixin_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mixin_integration_spec

Mixin and Static Polymorphism Integration Tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/mixin_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Mixin and Static Polymorphism Integration Tests.
Validates combining mixins with type classes for powerful abstractions
including mixin-provided instances, constraints, and default implementations.

## Scenarios

### Mixin + Static Polymorphism Integration

#### Mixin implementing type class

#### mixin provides type class instance

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mixin_is_instance = true
expect mixin_is_instance
```

</details>

#### class using mixin satisfies type class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val class_satisfies = true
expect class_satisfies
```

</details>

#### Generic mixin with type class constraints

#### mixin requires type class on parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val constraint_on_param = true
expect constraint_on_param
```

</details>

#### validates at application site

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validation_works = true
expect validation_works
```

</details>

#### Type class methods in mixin

#### mixin can use type class methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods_available = true
expect methods_available
```

</details>

#### correct dispatch for concrete types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatch_correct = true
expect dispatch_correct
```

</details>

#### Mixin composition with type classes

#### combines multiple mixins with type classes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val composition_works = true
expect composition_works
```

</details>

#### all constraints satisfied

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_constraints_met = true
expect all_constraints_met
```

</details>

#### Default implementations via mixins

#### mixin provides default type class methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defaults_via_mixin = true
expect defaults_via_mixin
```

</details>

#### selective override possible

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val selective_override = true
expect selective_override
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
