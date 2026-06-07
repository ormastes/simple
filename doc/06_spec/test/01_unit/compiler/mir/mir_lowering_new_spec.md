# Mir Lowering New Specification

> <details>

<!-- sdn-diagram:id=mir_lowering_new_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_lowering_new_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_lowering_new_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_lowering_new_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Lowering New Specification

## Scenarios

### Mir Lowering New

#### keeps MirLowering state shape available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/mir_lowering_types.spl")

expect(source).to_contain("struct MirLowering")
expect(source).to_contain("builder: MirBuilder")
expect(source).to_contain("symbols: SymbolTable")
```

</details>

#### keeps MirLowering constructor wired to HIR symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_mir_source("src/compiler/50.mir/mir_lowering_part2_part1.spl")

expect(source).to_contain("static fn new(symbols: SymbolTable) -> MirLowering")
expect(source).to_contain("symbols: symbols")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_lowering_new_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mir Lowering New

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
