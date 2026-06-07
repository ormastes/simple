# RV64 Pipeline Control Unit Tests

> Unit tests for 64-bit pipeline hazard detection and data forwarding.

<!-- sdn-diagram:id=rv64_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_pipeline_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Pipeline Control Unit Tests

Unit tests for 64-bit pipeline hazard detection and data forwarding.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-PIPELINE-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for 64-bit pipeline hazard detection and data forwarding.

## Scenarios

### Load-Use Hazard Detection

#### LD followed by dependent ALU detects hazard

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 10,
    id_rs1: 10, id_rs2: 0
)
expect(hazard).to_equal(true)
```

</details>

#### LD followed by independent ALU has no hazard

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 10,
    id_rs1: 11, id_rs2: 12
)
expect(hazard).to_equal(false)
```

</details>

#### non-load instruction has no load-use hazard

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hazard = detect_load_use_hazard(
    ex_is_load: false, ex_rd: 10,
    id_rs1: 10, id_rs2: 0
)
expect(hazard).to_equal(false)
```

</details>

#### hazard on rs2 dependency

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 10,
    id_rs1: 0, id_rs2: 10
)
expect(hazard).to_equal(true)
```

</details>

#### no hazard when ex_rd is x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 0,
    id_rs1: 0, id_rs2: 0
)
expect(hazard).to_equal(false)
```

</details>

#### LW also triggers hazard

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hazard = detect_load_use_hazard(
    ex_is_load: true, ex_rd: 5,
    id_rs1: 5, id_rs2: 0
)
expect(hazard).to_equal(true)
```

</details>

### Data Forwarding

#### forward from EX stage to rs1

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fwd = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 10, ex_write_en: true,
    mem_rd: 0, mem_write_en: false
)
expect(fwd == ForwardSrc.FromEx).to_equal(true)
```

</details>

#### forward from MEM stage to rs1

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fwd = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 0, ex_write_en: false,
    mem_rd: 10, mem_write_en: true
)
expect(fwd == ForwardSrc.FromMem).to_equal(true)
```

</details>

#### no forwarding when no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fwd = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 11, ex_write_en: true,
    mem_rd: 12, mem_write_en: true
)
expect(fwd == ForwardSrc.RegFile).to_equal(true)
```

</details>

#### no forwarding when rd is x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fwd = resolve_forward_rs1(
    id_rs1: 0,
    ex_rd: 0, ex_write_en: true,
    mem_rd: 0, mem_write_en: true
)
expect(fwd == ForwardSrc.RegFile).to_equal(true)
```

</details>

#### EX has priority over MEM

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fwd = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 10, ex_write_en: true,
    mem_rd: 10, mem_write_en: true
)
expect(fwd == ForwardSrc.FromEx).to_equal(true)
```

</details>

### Pipeline Control

#### stall on load-use hazard

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = compute_pipeline_control(
    load_use_hazard: true, branch_taken: false
)
expect(ctrl.stall).to_equal(true)
expect(ctrl.flush).to_equal(false)
```

</details>

#### flush on branch taken

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = compute_pipeline_control(
    load_use_hazard: false, branch_taken: true
)
expect(ctrl.stall).to_equal(false)
expect(ctrl.flush).to_equal(true)
```

</details>

#### no stall or flush in normal operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = compute_pipeline_control(
    load_use_hazard: false, branch_taken: false
)
expect(ctrl.stall).to_equal(false)
expect(ctrl.flush).to_equal(false)
```

</details>

### 64-bit Forwarding Paths

#### LD creates 64-bit forwarding path

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fwd = resolve_forward_rs2(
    id_rs2: 10,
    ex_rd: 10, ex_write_en: true,
    mem_rd: 0, mem_write_en: false
)
expect(fwd == ForwardSrc.FromEx).to_equal(true)
```

</details>

#### SD with forwarded store data

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fwd = resolve_forward_rs2(
    id_rs2: 11,
    ex_rd: 11, ex_write_en: true,
    mem_rd: 0, mem_write_en: false
)
expect(fwd == ForwardSrc.FromEx).to_equal(true)
```

</details>

#### double forwarding: both rs1 and rs2 from different stages

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fwd1 = resolve_forward_rs1(
    id_rs1: 10,
    ex_rd: 10, ex_write_en: true,
    mem_rd: 0, mem_write_en: false
)
val fwd2 = resolve_forward_rs2(
    id_rs2: 11,
    ex_rd: 0, ex_write_en: false,
    mem_rd: 11, mem_write_en: true
)
expect(fwd1 == ForwardSrc.FromEx).to_equal(true)
expect(fwd2 == ForwardSrc.FromMem).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
