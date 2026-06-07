# Packed Struct E2e Specification

> 1. var f: TestFlags = TestFlags new

<!-- sdn-diagram:id=packed_struct_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=packed_struct_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

packed_struct_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=packed_struct_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packed Struct E2e Specification

## Scenarios

### bitfield existing syntax e2e

#### round-trips field read/write

1. var f: TestFlags = TestFlags new
   - Expected: f.a equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f: TestFlags = TestFlags.new(0)
f.a = 3
expect(f.a).to_equal(3)
```

</details>

#### preserves adjacent fields on write

1. var f: TestFlags = TestFlags new
   - Expected: f.a equals `3`
   - Expected: f.b equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f: TestFlags = TestFlags.new(0)
f.a = 3
f.b = 5
expect(f.a).to_equal(3)
expect(f.b).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/packed_struct_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bitfield existing syntax e2e

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
