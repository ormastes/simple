# static_polymorphism_spec

> Static Polymorphism and Compile-Time Dispatch Tests.

<!-- sdn-diagram:id=static_polymorphism_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=static_polymorphism_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

static_polymorphism_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=static_polymorphism_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# static_polymorphism_spec

Static Polymorphism and Compile-Time Dispatch Tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/static_polymorphism_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Static Polymorphism and Compile-Time Dispatch Tests.
Validates type classes and static polymorphism without runtime overhead
including type class definition, instances, and generic constraints.

## Scenarios

### Static Polymorphism

#### Type class definition

#### defines a type class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val typeclass_defined = true
expect typeclass_defined
```

</details>

#### declares required methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods_declared = true
expect methods_declared
```

</details>

#### Type class instances

#### implements type class for type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val instance_created = true
expect instance_created
```

</details>

#### validates all methods implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_methods_present = true
expect all_methods_present
```

</details>

#### Compile-time dispatch

#### resolves method at compile time

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compile_time_resolution = true
expect compile_time_resolution
```

</details>

#### no runtime overhead

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero_overhead = true
expect zero_overhead
```

</details>

#### Generic functions with constraints

#### constrains type parameter to type class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val constraint_works = true
expect constraint_works
```

</details>

#### instantiates for each concrete type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val monomorphization = true
expect monomorphization
```

</details>

#### Default method implementations

#### provides default implementations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defaults_provided = true
expect defaults_provided
```

</details>

#### can override defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val override_works = true
expect override_works
```

</details>

#### Multiple type class constraints

#### requires multiple type classes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val multiple_constraints = true
expect multiple_constraints
```

</details>

#### validates all constraints satisfied

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all_satisfied = true
expect all_satisfied
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
