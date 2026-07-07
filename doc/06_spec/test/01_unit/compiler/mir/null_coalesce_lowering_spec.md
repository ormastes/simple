# Null Coalesce Lowering Specification

> <details>

<!-- sdn-diagram:id=null_coalesce_lowering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=null_coalesce_lowering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

null_coalesce_lowering_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=null_coalesce_lowering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Null Coalesce Lowering Specification

## Scenarios

### MIR null coalesce lowering

#### keeps null coalesce from falling through to nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_source("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")

expect(source).to_contain("case NullCoalesce(left, right):")
expect(source).to_contain("b_nc.terminate_if(mir_operand_copy(cond_local), then_block, else_block)")
expect(source).to_contain("b_right_done.emit_copy(result_local, right_local)")
expect(source).to_contain("if name == \"OUTPUT_LIMIT\":")
expect(source).to_contain("elif name == \"DEFAULT_TIMEOUT_MS\":")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/null_coalesce_lowering_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MIR null coalesce lowering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
