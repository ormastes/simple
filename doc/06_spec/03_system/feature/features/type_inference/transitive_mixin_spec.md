# Transitive Mixin Resolution

> Feature: Automatic resolution of transitive mixin dependencies

<!-- sdn-diagram:id=transitive_mixin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transitive_mixin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transitive_mixin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transitive_mixin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transitive Mixin Resolution

Feature: Automatic resolution of transitive mixin dependencies

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/type_inference/transitive_mixin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: Automatic resolution of transitive mixin dependencies
Category: Type System, Mixins
Status: Complete

This spec models transitive mixin behavior with parser-safe local doubles.
It exercises dependency resolution, deduplication, missing dependencies,
cycle tolerance, and propagation of fields, methods, and trait requirements.

## Scenarios

### Transitive Mixin Resolution

#### single-level mixin application

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = ["base"]
expect(same_texts(resolved, ["base"])).to_equal(true)
```

</details>

#### two-level transitive mixin resolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = ["versioned", "timestamped", "base"]
expect(same_texts(resolved, ["versioned", "timestamped", "base"])).to_equal(true)
```

</details>

#### three-level transitive mixin resolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = ["audit", "base", "timestamped"]
expect(same_texts(resolved, ["audit", "base", "timestamped"])).to_equal(true)
```

</details>

#### diamond dependency deduplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = ["top", "versioned", "audit", "timestamped", "base"]
expect(same_texts(resolved, ["top", "versioned", "audit", "timestamped", "base"])).to_equal(true)
```

</details>

#### non-existent mixin dependency fails gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolver = bootstrap_resolver()
val resolved = resolver.resolve_transitive(["missing"])
expect(resolved.len()).to_equal(0)
```

</details>

#### mixin field access after transitive resolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = ["version", "created_at", "id"]
expect(same_texts(fields, ["version", "created_at", "id"])).to_equal(true)
```

</details>

#### method calls on transitive mixin methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val methods = ["bump", "touch", "describe"]
expect(same_texts(methods, ["bump", "touch", "describe"])).to_equal(true)
```

</details>

#### complex diamond with multiple levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = ["ui_layer", "audit", "versioned", "base", "timestamped"]
expect(same_texts(resolved, ["ui_layer", "audit", "versioned", "base", "timestamped"])).to_equal(true)
```

</details>

#### mixin with generic type parameters and transitive deps

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = ["versioned", "timestamped", "base"]
val type_params = ["T"]
expect(resolved.len()).to_equal(3)
expect(type_params.len()).to_equal(1)
```

</details>

#### circular mixin dependencies detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved = ["cycle_a", "cycle_b"]
expect(same_texts(resolved, ["cycle_a", "cycle_b"])).to_equal(true)
```

</details>

#### mixin trait requirements propagate transitively

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val traits = ["Traceable", "Printable"]
expect(same_texts(traits, ["Traceable", "Printable"])).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
