# STM32U5 Target Definition Specification

> Verifies `Stm32U5Target` creation, memory layout, core delegation, and probe configuration. The target wraps `ArmCortexMTarget.cortex_m33()` with STM32U585-specific memory addresses.

<!-- sdn-diagram:id=stm32u5_target_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stm32u5_target_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stm32u5_target_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stm32u5_target_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STM32U5 Target Definition Specification

Verifies `Stm32U5Target` creation, memory layout, core delegation, and probe configuration. The target wraps `ArmCortexMTarget.cortex_m33()` with STM32U585-specific memory addresses.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UNOQ-PORT |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/debug/remote/target/stm32u5_target_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies `Stm32U5Target` creation, memory layout, core delegation,
and probe configuration. The target wraps `ArmCortexMTarget.cortex_m33()`
with STM32U585-specific memory addresses.

## Behavior

- Default factory uses `interface/stlink.cfg` probe
- `with_probe()` overrides probe config
- Flash base at 0x08000000
- SRAM base at 0x20000000, size 786432 (786 KB)
- Core name delegates to "Cortex-M33"
- 8 HW breakpoints, 4 HW watchpoints (M33 spec)

## Scenarios

### Stm32U5Target default

#### AC-2: name is STM32U5 (Cortex-M33)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.default()
expect(t.name()).to_equal("STM32U5 (Cortex-M33)")
```

</details>

#### AC-2: flash_base is 0x08000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.default()
expect(t.flash_base()).to_equal(0x08000000)
```

</details>

#### AC-2: sram_base is 0x20000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.default()
expect(t.sram_base()).to_equal(0x20000000)
```

</details>

#### AC-2: sram_size is 786432

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.default()
val ss = t.sram_size()
expect(ss).to_equal(786432)
```

</details>

### Stm32U5Target core delegation

#### AC-2: core_name is Cortex-M33

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.default()
expect(t.core_name()).to_equal("Cortex-M33")
```

</details>

#### AC-2: hw_breakpoint_count is 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.default()
val bp = t.hw_breakpoint_count()
expect(bp).to_equal(8)
```

</details>

#### AC-2: hw_watchpoint_count is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.default()
val wp = t.hw_watchpoint_count()
expect(wp).to_equal(4)
```

</details>

#### AC-2: word_size is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.default()
val ws = t.word_size()
expect(ws).to_equal(4)
```

</details>

### Stm32U5Target with_probe

#### AC-2: with_probe overrides probe_cfg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.with_probe("interface/jlink.cfg")
expect(t.probe_cfg).to_equal("interface/jlink.cfg")
```

</details>

#### AC-2: with_probe preserves name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.with_probe("interface/cmsis-dap.cfg")
expect(t.name()).to_equal("STM32U5 (Cortex-M33)")
```

</details>

#### AC-2: default probe_cfg is interface/stlink.cfg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = Stm32U5Target.default()
expect(t.probe_cfg).to_equal("interface/stlink.cfg")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
