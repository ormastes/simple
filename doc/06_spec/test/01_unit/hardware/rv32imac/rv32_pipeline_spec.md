# RV32 Pipeline Control Unit Tests

> Unit tests for pipeline hazard detection, forwarding, and control signals.

<!-- sdn-diagram:id=rv32_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_pipeline_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 Pipeline Control Unit Tests

Unit tests for pipeline hazard detection, forwarding, and control signals.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-PIPELINE-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/hardware/rv32imac/rv32_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for pipeline hazard detection, forwarding, and control signals.

## Scenarios

### Load-Use Hazard Detection

#### detects hazard on rs1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_load_use_hazard(5, 0, 5, MemOp.Load, true)).to_equal(true)
```

</details>

#### detects hazard on rs2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_load_use_hazard(0, 5, 5, MemOp.Load, true)).to_equal(true)
```

</details>

#### no hazard for non-load

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_load_use_hazard(5, 0, 5, MemOp.Store, true)).to_equal(false)
expect(detect_load_use_hazard(5, 0, 5, MemOp.None, true)).to_equal(false)
```

</details>

#### no hazard when EX invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_load_use_hazard(5, 0, 5, MemOp.Load, false)).to_equal(false)
```

</details>

#### no hazard when rd is x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_load_use_hazard(0, 3, 0, MemOp.Load, true)).to_equal(false)
```

</details>

#### no hazard when no register match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_load_use_hazard(3, 4, 5, MemOp.Load, true)).to_equal(false)
```

</details>

### Data Forwarding

#### forwards from EX stage when match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_forward_rs1(5, 5, true, 0, false) == ForwardSrc.ExStage).to_equal(true)
```

</details>

#### forwards from MEM stage when EX doesn't match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_forward_rs1(5, 3, true, 5, true) == ForwardSrc.MemStage).to_equal(true)
```

</details>

#### uses regfile when no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_forward_rs1(5, 3, true, 4, true) == ForwardSrc.RegFile).to_equal(true)
```

</details>

#### x0 always from regfile

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_forward_rs1(0, 0, true, 0, true) == ForwardSrc.RegFile).to_equal(true)
```

</details>

#### EX has priority over MEM

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_forward_rs1(5, 5, true, 5, true) == ForwardSrc.ExStage).to_equal(true)
```

</details>

### Pipeline Control Signals

#### normal operation - no stalls or flushes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = compute_pipeline_control(false, false, false)
expect(ctrl.stall_if).to_equal(false)
expect(ctrl.stall_id).to_equal(false)
expect(ctrl.flush_if).to_equal(false)
expect(ctrl.flush_id).to_equal(false)
expect(ctrl.flush_ex).to_equal(false)
```

</details>

#### load-use: stalls IF/ID, flushes EX

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = compute_pipeline_control(true, false, false)
expect(ctrl.stall_if).to_equal(true)
expect(ctrl.stall_id).to_equal(true)
expect(ctrl.flush_ex).to_equal(true)
expect(ctrl.flush_if).to_equal(false)
```

</details>

#### branch taken: flushes IF/ID

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = compute_pipeline_control(false, true, false)
expect(ctrl.flush_if).to_equal(true)
expect(ctrl.flush_id).to_equal(true)
expect(ctrl.stall_if).to_equal(false)
```

</details>

#### trap: flushes everything

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = compute_pipeline_control(false, false, true)
expect(ctrl.flush_if).to_equal(true)
expect(ctrl.flush_id).to_equal(true)
expect(ctrl.flush_ex).to_equal(true)
```

</details>

#### branch overrides load-use stall

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = compute_pipeline_control(true, true, false)
expect(ctrl.flush_if).to_equal(true)
expect(ctrl.stall_if).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
