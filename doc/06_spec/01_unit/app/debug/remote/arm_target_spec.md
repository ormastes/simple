# Arm Target Specification

> <details>

<!-- sdn-diagram:id=arm_target_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm_target_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm_target_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm_target_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm Target Specification

## Scenarios

### ArmCortexMTarget Cortex-M7

#### has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.name()).to_equal("ARM Cortex-M7")
```

</details>

#### has correct core name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.core_name()).to_equal("Cortex-M7")
```

</details>

#### has 21 registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_count()).to_equal(21)
```

</details>

#### has 6 HW breakpoints for M7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.hw_breakpoint_count()).to_equal(6)
```

</details>

#### has 4 HW watchpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.hw_watchpoint_count()).to_equal(4)
```

</details>

### ArmCortexMTarget Cortex-M4

#### has correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m4()
expect(t.name()).to_equal("ARM Cortex-M4")
```

</details>

#### has 4 HW breakpoints for M4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m4()
expect(t.hw_breakpoint_count()).to_equal(4)
```

</details>

### ArmCortexMTarget register lookups

#### r0 is index 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("r0")).to_equal(0)
```

</details>

#### pc is index 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("pc")).to_equal(15)
```

</details>

#### sp is index 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("sp")).to_equal(13)
```

</details>

#### xPSR is index 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("xPSR")).to_equal(16)
```

</details>

#### unknown register returns -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("nonexistent")).to_equal(-1)
```

</details>

#### register_name at 0 is r0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_name(0)).to_equal("r0")
```

</details>

#### register_name out of bounds is unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_name(100)).to_equal("unknown")
```

</details>

### ArmCortexMTarget breakpoint

#### thumb BKPT instruction is 0x00 0xBE

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
val bkpt = t.breakpoint_instruction()
expect(bkpt.len()).to_equal(2)
expect(bkpt[0]).to_equal(0)
expect(bkpt[1]).to_equal(190)
```

</details>

#### word size is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.word_size()).to_equal(4)
```

</details>

#### supports single step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = ArmCortexMTarget.cortex_m7()
expect(t.supports_single_step()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/arm_target_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ArmCortexMTarget Cortex-M7
- ArmCortexMTarget Cortex-M4
- ArmCortexMTarget register lookups
- ArmCortexMTarget breakpoint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
