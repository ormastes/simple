# Flat Ast Inline Asm Bridge Specification

> <details>

<!-- sdn-diagram:id=flat_ast_inline_asm_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=flat_ast_inline_asm_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

flat_ast_inline_asm_bridge_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=flat_ast_inline_asm_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Flat Ast Inline Asm Bridge Specification

## Scenarios

### Flat AST bridge inline asm fidelity

#### preserves inline asm as typed AsmBlock nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn test():\n    asm(\"cli\")\n"
expect(first_asm_template(src)).to_equal("cli")
```

</details>

#### preserves volatile asm text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "fn test():\n    asm volatile(\"bkpt #0\")\n"
expect(first_asm_template(src)).to_equal("bkpt #0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/flat_ast_inline_asm_bridge_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Flat AST bridge inline asm fidelity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
