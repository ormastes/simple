# Macros Specification

> Tests for the macro system including macro definitions, expansions, hygiene, and integration with the compiler's metaprogramming capabilities.

<!-- sdn-diagram:id=macros_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macros_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macros_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macros_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macros Specification

Tests for the macro system including macro definitions, expansions, hygiene, and integration with the compiler's metaprogramming capabilities.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 4/5 |
| Status | Planned |
| Source | `test/03_system/feature/usage/macros_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the macro system including macro definitions, expansions,
hygiene, and integration with the compiler's metaprogramming capabilities.

## Syntax

```simple
macro my_macro(param) -> Result:
# Macro body with code generation
quote:
val result = ~param * 2
result
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Macro Definition | Compile-time code template generation |
| Hygiene | Prevention of variable name collisions in macro expansion |
| Quote/Unquote | Syntax for code as data and interpolation |
| Expansion | Runtime substitution of macro calls with generated code |

## Behavior

- Macros execute at compile-time to generate code
- Proper hygiene ensures macro-generated variables don't shadow user code
- Supports nested macros and recursive expansion
- Quote-unquote syntax for metaprogramming
- Error handling during macro expansion

## Related Specifications

- Generators - Similar metaprogramming concepts
- Code Generation - Template expansion and code synthesis

## Scenarios

### Macros Basic Definition and Expansion

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement basic macro tests when macro system is available
expect true
```

</details>

### Macros Hygiene

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement macro hygiene tests
expect true
```

</details>

### Macros Advanced Features

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement advanced macro feature tests
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
