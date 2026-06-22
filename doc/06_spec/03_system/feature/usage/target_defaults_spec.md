# Target-Based Mutability Defaults

> Simple supports target-based compilation modes that change the default mutability of collections. In the general (default) target, arrays and dicts are mutable, allowing `push` and key assignment without explicit `var` declarations. Under `--target=embedded`, collections default to immutable to reduce memory overhead and prevent accidental mutation in resource-constrained environments. This spec validates the general-mode mutable defaults for arrays and dicts.

<!-- sdn-diagram:id=target_defaults_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=target_defaults_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

target_defaults_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=target_defaults_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target-Based Mutability Defaults

Simple supports target-based compilation modes that change the default mutability of collections. In the general (default) target, arrays and dicts are mutable, allowing `push` and key assignment without explicit `var` declarations. Under `--target=embedded`, collections default to immutable to reduce memory overhead and prevent accidental mutation in resource-constrained environments. This spec validates the general-mode mutable defaults for arrays and dicts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-009 |
| Category | Language |
| Status | In Progress |
| Source | `test/03_system/feature/usage/target_defaults_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple supports target-based compilation modes that change the default mutability of
collections. In the general (default) target, arrays and dicts are mutable, allowing
`push` and key assignment without explicit `var` declarations. Under `--target=embedded`,
collections default to immutable to reduce memory overhead and prevent accidental mutation
in resource-constrained environments. This spec validates the general-mode mutable
defaults for arrays and dicts.

## Syntax

```simple
var arr = [1, 2, 3]
arr.push(4)
expect arr.len() == 4

val dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Target Mode | A compile-time flag (`--target=`) that sets platform-specific defaults |
| General Mode | Default target where arrays and dicts are mutable out of the box |
| Embedded Mode | Target where collections default to immutable for safety and efficiency |
| Mutability Default | Whether a collection allows modification without an explicit `var` binding |

## Scenarios

### Target-Based Mutability Defaults

#### General Mode (Default)

#### makes arrays mutable by default

1. arr push
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr.push(4)
expect arr[3] == 4
expect arr.len() == 4
```

</details>

#### makes dicts mutable by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = {"a": 1}
dict["b"] = 2
expect dict["b"] == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
