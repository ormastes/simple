# Cortex-M33 Target Preset Specification

> Verifies that `preset_cortex_m33()` returns the correct ARMv8-M Mainline target configuration and that it integrates with `preset_by_name()` and `preset_all_names()`.

<!-- sdn-diagram:id=target_presets_m33_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=target_presets_m33_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

target_presets_m33_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=target_presets_m33_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cortex-M33 Target Preset Specification

Verifies that `preset_cortex_m33()` returns the correct ARMv8-M Mainline target configuration and that it integrates with `preset_by_name()` and `preset_all_names()`.

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
| Source | `test/01_unit/compiler/backend/target_presets_m33_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that `preset_cortex_m33()` returns the correct ARMv8-M Mainline
target configuration and that it integrates with `preset_by_name()` and
`preset_all_names()`.

## Behavior

- arch must be `thumbv8m.main` (ARMv8-M Mainline, not thumbv7em)
- ABI must be `eabihf` (STM32U585 has hardware FPU)
- Float support enabled
- Stack size 16384 (larger SRAM allows bigger stack than M4 default)
- Pointer width 32 (Cortex-M33 is 32-bit)
- Discoverable via `preset_by_name("cortex-m33")`
- Listed in `preset_all_names()`

## Scenarios

### preset_cortex_m33

#### AC-1: arch is thumbv8m.main

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = preset_cortex_m33()
expect(p.arch).to_equal("thumbv8m.main")
```

</details>

#### AC-1: abi is eabihf

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = preset_cortex_m33()
expect(p.abi).to_equal("eabihf")
```

</details>

#### AC-1: float_support is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = preset_cortex_m33()
expect(p.float_support).to_equal(true)
```

</details>

#### AC-1: stack_size is 16384

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = preset_cortex_m33()
expect(p.stack_size).to_equal(16384)
```

</details>

#### AC-1: pointer_width is 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = preset_cortex_m33()
expect(p.pointer_width).to_equal(32)
```

</details>

### preset_cortex_m33 discovery

#### AC-1: preset_by_name returns cortex-m33 with correct arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = preset_by_name("cortex-m33")
expect(p.arch).to_equal("thumbv8m.main")
```

</details>

#### AC-1: preset_all_names contains cortex-m33

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = preset_all_names()
expect(names).to_contain("cortex-m33")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
