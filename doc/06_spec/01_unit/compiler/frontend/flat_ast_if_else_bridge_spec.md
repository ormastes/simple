# Flat Ast If Else Bridge Specification

> <details>

<!-- sdn-diagram:id=flat_ast_if_else_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=flat_ast_if_else_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

flat_ast_if_else_bridge_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=flat_ast_if_else_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Flat Ast If Else Bridge Specification

## Scenarios

### Flat AST bridge if/else fidelity (M12 item 6)

#### attaches the else block for if/else

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn f(n: i64) -> i64:\n    if n > 0:\n        return 1\n    else:\n        return 2\n"
expect(if_else_else_count(src, "f")).to_equal(1)
```

</details>

#### leaves else nil for a plain if (no spurious empty else block)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn g(n: i64) -> i64:\n    if n > 0:\n        return 1\n    return 0\n"
expect(if_else_else_count(src, "g")).to_equal(-2)
```

</details>

#### attaches the else chain for if/elif/else

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn h(n: i64) -> i64:\n    if n > 90:\n        return 1\n    elif n > 50:\n        return 2\n    else:\n        return 3\n"
expect(if_else_else_count(src, "h")).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Flat AST bridge if/else fidelity (M12 item 6)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
