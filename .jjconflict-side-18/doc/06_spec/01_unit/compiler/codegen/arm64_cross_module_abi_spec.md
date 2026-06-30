# Arm64 Cross Module Abi Specification

> <details>

<!-- sdn-diagram:id=arm64_cross_module_abi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm64_cross_module_abi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm64_cross_module_abi_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm64_cross_module_abi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Cross Module Abi Specification

## Scenarios

### arm64 cross-module ABI contracts

#### pointer width — LP64

#### macos-arm64 preset has 64-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_macos_arm64()
expect(preset.pointer_width).to_equal(64)
```

</details>

#### cortex-m4 has 32-bit pointers (contrast)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Cross-module pointer loads on Cortex-M must NOT be widened to 64-bit.
val preset = preset_cortex_m4()
expect(preset.pointer_width).to_equal(32)
```

</details>

#### arm64 and cortex-m4 pointer widths differ

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64 = preset_macos_arm64()
val cm4 = preset_cortex_m4()
expect(arm64.pointer_width == cm4.pointer_width).to_equal(false)
```

</details>

#### ABI — AAPCS64 / macho

#### macos-arm64 preset ABI is macho

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_macos_arm64()
expect(preset.abi).to_equal("macho")
```

</details>

#### macos-arm64 preset arch is aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_macos_arm64()
expect(preset.arch).to_equal("aarch64")
```

</details>

#### macos-arm64 preset OS is macos

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_macos_arm64()
expect(preset.os).to_equal("macos")
```

</details>

#### macos-arm64 has float support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_macos_arm64()
expect(preset.float_support).to_equal(true)
```

</details>

#### target family classification

#### aarch64-apple-macosx triple classifies as Aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val family = target_family_from_triple("aarch64-apple-macosx")
expect(family).to_equal("Aarch64")
```

</details>

#### arm64-apple-macosx triple also classifies as Aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both aarch64-* and arm64-* must map to Aarch64.
# A regression here would cause the compiler to mis-apply x86 or
# Arm32 ABI selection to cross-module calls on Apple Silicon.
val family = target_family_from_triple("arm64-apple-macosx")
expect(family).to_equal("Aarch64")
```

</details>

#### aarch64-unknown-linux-gnu classifies as Aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val family = target_family_from_triple("aarch64-unknown-linux-gnu")
expect(family).to_equal("Aarch64")
```

</details>

#### thumbv7em triple classifies as Arm32 not Aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Cortex-M4 (Thumb2 / ARMv7-M) must be Arm32, not Aarch64.
# Misclassification would apply LP64 ABI to a 32-bit MCU.
val family = target_family_from_triple("thumbv7em-none-eabihf")
expect(family).to_equal("Arm32")
```

</details>

#### thumbv6m triple does not classify as Aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: target_family_from_triple recognises "thumbv7" as Arm32
# but not "thumbv6m" (it falls through to Unknown). Either way,
# it must NOT be classified as Aarch64, which would apply LP64 ABI
# to a 32-bit Cortex-M0 target.
val family = target_family_from_triple("thumbv6m-none-eabi")
expect(family == "Aarch64").to_equal(false)
```

</details>

#### x86_64 triple does not classify as Aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val family = target_family_from_triple("x86_64-unknown-linux-gnu")
expect(family == "Aarch64").to_equal(false)
```

</details>

#### module-level val safety (non-baremetal)

#### macos-arm64 is NOT a baremetal preset

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The Mach-O loader initialises BSS before main(), so module-level
# val constants are NOT zero. Baremetal val-zero bug is scoped to
# no_std=true targets only.
val preset = preset_macos_arm64()
expect(preset_is_baremetal(preset)).to_equal(false)
```

</details>

#### macos-arm64 has no_std=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_macos_arm64()
expect(preset.no_std).to_equal(false)
```

</details>

#### cortex-m4 IS a baremetal preset (contrast)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Cortex-M4 targets DO have the val-zero risk if BSS is cleared
# before runtime-init; module-level vals must use function-local form.
val preset = preset_cortex_m4()
expect(preset_is_baremetal(preset)).to_equal(true)
```

</details>

#### cortex-m0 IS a baremetal preset (contrast)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preset = preset_cortex_m0()
expect(preset_is_baremetal(preset)).to_equal(true)
```

</details>

#### CodegenTarget AArch64 variant

#### CodegenTarget.AArch64 to_text is aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The to_text method drives symbol mangling in cross-module imports.
# A regression (e.g. returning arm64 or armv8) would break import
# symbol resolution for AArch64 cross-module calls.
val target = CodegenTarget.AArch64
expect(target.to_text()).to_equal("aarch64")
```

</details>

#### CodegenTarget.AArch64 is_64bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = CodegenTarget.AArch64
expect(target.is_64bit()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/arm64_cross_module_abi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- arm64 cross-module ABI contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
