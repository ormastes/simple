# Union Type Declarations and Discrimination

> Union types allow a variable to hold a value of one of several specified types, written as `A | B`. At runtime the language provides type discrimination so that pattern matching or type-checking can narrow a union back to a concrete type. This spec is a placeholder that will be expanded once the union type feature lands; the planned coverage includes declaring union type annotations, assigning values of different member types, and narrowing via `match` with type-case arms.

<!-- sdn-diagram:id=union_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=union_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

union_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=union_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Union Type Declarations and Discrimination

Union types allow a variable to hold a value of one of several specified types, written as `A | B`. At runtime the language provides type discrimination so that pattern matching or type-checking can narrow a union back to a concrete type. This spec is a placeholder that will be expanded once the union type feature lands; the planned coverage includes declaring union type annotations, assigning values of different member types, and narrowing via `match` with type-case arms.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-034 |
| Category | Language |
| Status | Planned |
| Source | `test/03_system/feature/usage/union_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Union types allow a variable to hold a value of one of several specified types,
written as `A | B`. At runtime the language provides type discrimination so that
pattern matching or type-checking can narrow a union back to a concrete type.
This spec is a placeholder that will be expanded once the union type feature
lands; the planned coverage includes declaring union type annotations, assigning
values of different member types, and narrowing via `match` with type-case arms.

## Syntax

```simple
# Planned union type declaration (not yet implemented)
val value: Int | Str = 42

# Planned pattern-match narrowing
match value:
case Int(n): print("number: {n}")
case Str(s): print("string: {s}")
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Union type (`A \| B`) | A type that can hold a value belonging to any of its member types |
| Type discrimination | Runtime mechanism to determine which member type a union value actually is |
| Pattern narrowing | Using `match` with type-case arms to safely extract the concrete value |
| Planned status | Feature is not yet implemented; spec contains a placeholder test only |

## Scenarios

### Union Types

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement union type tests when feature is available
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
