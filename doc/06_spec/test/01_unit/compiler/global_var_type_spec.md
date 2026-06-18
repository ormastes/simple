# Global Var Type Specification

> <details>

<!-- sdn-diagram:id=global_var_type_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=global_var_type_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

global_var_type_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=global_var_type_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Global Var Type Specification

## Scenarios

### Module-level typed variable declarations

#### var g_addr: u64 preserves integer addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(compute_address()).to_equal(0xFD001000)
```

</details>

#### var g_count: u64 preserves integer arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(increment_count()).to_equal(101)
```

</details>

#### val g_offset: u64 preserves value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(g_offset).to_equal(0x1000)
```

</details>

#### var g_signed: i64 supports negative values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(signed_add()).to_equal(10)
```

</details>

#### module-level var can be mutated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
g_count = 200
expect(g_count).to_equal(200)
g_count = 100
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/global_var_type_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module-level typed variable declarations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
