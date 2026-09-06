# Rv32 Decode Helper Hir Lowering Specification

> <details>

<!-- sdn-diagram:id=rv32_decode_helper_hir_lowering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_decode_helper_hir_lowering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_decode_helper_hir_lowering_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_decode_helper_hir_lowering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv32 Decode Helper Hir Lowering Specification

## Scenarios

### RV32 decode helper nil guards

#### keeps explicit nil rechecks on the shared symbol lookup paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val declaration_lowering = file_text("src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl")
val resolve_strategies = file_text("src/compiler/35.semantics/resolve_strategies.spl")

expect(declaration_lowering.contains("if found_symbol == nil:")).to_equal(true)
expect(resolve_strategies.contains("if type_id == nil:")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/rv32_decode_helper_hir_lowering_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV32 decode helper nil guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
