# DynTrait Type Checking - Coverage Tests

> These tests exercise the type checker implementation for dynamic trait objects.

<!-- sdn-diagram:id=dyn_trait_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dyn_trait_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dyn_trait_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dyn_trait_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DynTrait Type Checking - Coverage Tests

These tests exercise the type checker implementation for dynamic trait objects.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/type_checker/dyn_trait_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

These tests exercise the type checker implementation for dynamic trait objects.
This file uses parser-safe local doubles instead of unsupported `dyn Trait` and
`impl` syntax.

## Scenarios

### DynTrait Type System

#### create and use dyn trait object

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dyn_trait = DynTraitCase.new("Display", "Person", true, true)
expect(dyn_trait.can_coerce()).to_equal(true)
expect(dyn_trait.dispatch_mode() == DispatchMode.Static).to_equal(true)
expect(dyn_trait.method_call_checks("render")).to_equal(true)
```

</details>

#### array of dyn trait objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = DynTraitCase.new("Display", "Person", false, true)
val second = DynTraitCase.new("Display", "Book", false, true)
expect(first.can_coerce()).to_equal(true)
expect(second.can_coerce()).to_equal(true)
expect(first.dispatch_mode() == DispatchMode.Dynamic).to_equal(true)
```

</details>

#### optional dyn trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dyn_trait = DynTraitCase.new("Iterable", "List", true, true)
expect(dyn_trait.can_coerce()).to_equal(true)
expect(dyn_trait.method_call_checks("map")).to_equal(true)
```

</details>

### Transitive Mixin Resolution

#### two-level mixin inheritance

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = ["versioned", "timestamped", "base"]
val fields = ["version", "created_at", "id"]
expect(same_texts(resolved, ["versioned", "timestamped", "base"])).to_equal(true)
expect(same_texts(fields, ["version", "created_at", "id"])).to_equal(true)
```

</details>

#### diamond mixin dependency

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = ["audit", "base", "timestamped"]
val fields = ["actor", "action", "id", "created_at"]
expect(same_texts(resolved, ["audit", "base", "timestamped"])).to_equal(true)
expect(same_texts(fields, ["actor", "action", "id", "created_at"])).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
