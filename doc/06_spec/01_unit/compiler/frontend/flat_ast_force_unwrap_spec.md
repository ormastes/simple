# Flat Ast Force Unwrap Specification

> <details>

<!-- sdn-diagram:id=flat_ast_force_unwrap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=flat_ast_force_unwrap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

flat_ast_force_unwrap_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=flat_ast_force_unwrap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Flat Ast Force Unwrap Specification

## Scenarios

### Flat AST bridge ForceUnwrap fidelity (M12 item 7)

#### postfix ! produces a distinct ForceUnwrap node

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn f(x: i64) -> i64:\n    return x!\n"
expect(first_unwrap_kind(src)).to_equal("force-unwrap")
```

</details>

#### .? stays an ExistsCheck node (not conflated with !)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn g(x: i64) -> i64:\n    return x.?\n"
expect(first_unwrap_kind(src)).to_equal("exists-check")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/flat_ast_force_unwrap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Flat AST bridge ForceUnwrap fidelity (M12 item 7)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
