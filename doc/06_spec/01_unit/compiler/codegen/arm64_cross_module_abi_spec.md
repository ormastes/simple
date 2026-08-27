# Arm64 Cross Module Abi Specification

> Tests covering arm64 cross-module ABI contracts.

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

- macos-arm64 preset has 64-bit pointers
   - Expected: preset.pointer_width equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("macos-arm64 preset has 64-bit pointers")
val preset = preset_macos_arm64()
expect(preset.pointer_width).to_equal(64)
```

</details>

#### cortex-m4 has 32-bit pointers (contrast)

- cortex-m4 has 32-bit pointers (contrast)
   - Expected: preset.pointer_width equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("cortex-m4 has 32-bit pointers (contrast)")
# Cross-module pointer loads on Cortex-M must NOT be widened to 64-bit.
val preset = preset_cortex_m4()
expect(preset.pointer_width).to_equal(32)
```

</details>

#### arm64 and cortex-m4 pointer widths differ

- arm64 and cortex-m4 pointer widths differ


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("arm64 and cortex-m4 pointer widths differ")
val arm64 = preset_macos_arm64()
val cm4 = preset_cortex_m4()
expect(arm64.pointer_width).to_not_equal(cm4.pointer_width)
```

</details>

#### ABI — AAPCS64 / macho

#### macos-arm64 preset ABI is macho

- macos-arm64 preset ABI is macho
   - Expected: preset.abi equals `macho`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("macos-arm64 preset ABI is macho")
val preset = preset_macos_arm64()
expect(preset.abi).to_equal("macho")
```

</details>

#### macos-arm64 preset arch is aarch64

- macos-arm64 preset arch is aarch64
   - Expected: preset.arch equals `aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("macos-arm64 preset arch is aarch64")
val preset = preset_macos_arm64()
expect(preset.arch).to_equal("aarch64")
```

</details>

#### macos-arm64 preset OS is macos

- macos-arm64 preset OS is macos
   - Expected: preset.os equals `macos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("macos-arm64 preset OS is macos")
val preset = preset_macos_arm64()
expect(preset.os).to_equal("macos")
```

</details>

#### macos-arm64 has float support

- macos-arm64 has float support
   - Expected: preset.float_support is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("macos-arm64 has float support")
val preset = preset_macos_arm64()
expect(preset.float_support).to_equal(true)
```

</details>

#### target family classification

#### aarch64-apple-macosx triple classifies as Aarch64

- aarch64-apple-macosx triple classifies as Aarch64
   - Expected: family equals `Aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("aarch64-apple-macosx triple classifies as Aarch64")
val family = target_family_from_triple("aarch64-apple-macosx")
expect(family).to_equal("Aarch64")
```

</details>

#### arm64-apple-macosx triple also classifies as Aarch64

- arm64-apple-macosx triple also classifies as Aarch64
   - Expected: family equals `Aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("arm64-apple-macosx triple also classifies as Aarch64")
# Both aarch64-* and arm64-* must map to Aarch64.
# A regression here would cause the compiler to mis-apply x86 or
# Arm32 ABI selection to cross-module calls on Apple Silicon.
val family = target_family_from_triple("arm64-apple-macosx")
expect(family).to_equal("Aarch64")
```

</details>

#### aarch64-unknown-linux-gnu classifies as Aarch64

- aarch64-unknown-linux-gnu classifies as Aarch64
   - Expected: family equals `Aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("aarch64-unknown-linux-gnu classifies as Aarch64")
val family = target_family_from_triple("aarch64-unknown-linux-gnu")
expect(family).to_equal("Aarch64")
```

</details>

#### thumbv7em triple classifies as Arm32 not Aarch64

- thumbv7em triple classifies as Arm32 not Aarch64
   - Expected: family equals `Arm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("thumbv7em triple classifies as Arm32 not Aarch64")
# Cortex-M4 (Thumb2 / ARMv7-M) must be Arm32, not Aarch64.
# Misclassification would apply LP64 ABI to a 32-bit MCU.
val family = target_family_from_triple("thumbv7em-none-eabihf")
expect(family).to_equal("Arm32")
```

</details>

#### thumbv6m triple does not classify as Aarch64

- thumbv6m triple does not classify as Aarch64


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("thumbv6m triple does not classify as Aarch64")
# Note: target_family_from_triple recognises "thumbv7" as Arm32
# but not "thumbv6m" (it falls through to Unknown). Either way,
# it must NOT be classified as Aarch64, which would apply LP64 ABI
# to a 32-bit Cortex-M0 target.
val family = target_family_from_triple("thumbv6m-none-eabi")
expect(family).to_not_equal("Aarch64")
```

</details>

#### x86_64 triple does not classify as Aarch64

- x86_64 triple does not classify as Aarch64


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x86_64 triple does not classify as Aarch64")
val family = target_family_from_triple("x86_64-unknown-linux-gnu")
expect(family).to_not_equal("Aarch64")
```

</details>

#### module-level val safety (non-baremetal)

#### macos-arm64 is NOT a baremetal preset

- macos-arm64 is NOT a baremetal preset
   - Expected: preset_is_baremetal(preset) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("macos-arm64 is NOT a baremetal preset")
# The Mach-O loader initialises BSS before main(), so module-level
# val constants are NOT zero. Baremetal val-zero bug is scoped to
# no_std=true targets only.
val preset = preset_macos_arm64()
expect(preset_is_baremetal(preset)).to_equal(false)
```

</details>

#### macos-arm64 has no_std=false

- macos-arm64 has no_std=false
   - Expected: preset.no_std is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("macos-arm64 has no_std=false")
val preset = preset_macos_arm64()
expect(preset.no_std).to_equal(false)
```

</details>

#### cortex-m4 IS a baremetal preset (contrast)

- cortex-m4 IS a baremetal preset (contrast)
   - Expected: preset_is_baremetal(preset) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("cortex-m4 IS a baremetal preset (contrast)")
# Cortex-M4 targets DO have the val-zero risk if BSS is cleared
# before runtime-init; module-level vals must use function-local form.
val preset = preset_cortex_m4()
expect(preset_is_baremetal(preset)).to_equal(true)
```

</details>

#### cortex-m0 IS a baremetal preset (contrast)

- cortex-m0 IS a baremetal preset (contrast)
   - Expected: preset_is_baremetal(preset) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("cortex-m0 IS a baremetal preset (contrast)")
val preset = preset_cortex_m0()
expect(preset_is_baremetal(preset)).to_equal(true)
```

</details>

#### CodegenTarget AArch64 variant

#### CodegenTarget.AArch64 to_text is aarch64

- CodegenTarget.AArch64 to_text is aarch64
   - Expected: target.to_text() equals `aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CodegenTarget.AArch64 to_text is aarch64")
# The to_text method drives symbol mangling in cross-module imports.
# A regression (e.g. returning arm64 or armv8) would break import
# symbol resolution for AArch64 cross-module calls.
val target = CodegenTarget.AArch64
expect(target.to_text()).to_equal("aarch64")
```

</details>

#### CodegenTarget.AArch64 is_64bit

- CodegenTarget.AArch64 is_64bit
   - Expected: target.is_64bit() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CodegenTarget.AArch64 is_64bit")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering arm64 cross-module ABI contracts.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `64bdebfeded01326005eacb4c1553700a2882bd19cb84d2a99da049d498c26b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64bdebfeded01326005eacb4c1553700a2882bd19cb84d2a99da049d498c26b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64bdebfeded01326005eacb4c1553700a2882bd19cb84d2a99da049d498c26b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/codegen/arm64_cross_module_abi_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/arm64_cross_module_abi_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/arm64_cross_module_abi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/arm64_cross_module_abi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/arm64_cross_module_abi_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/codegen/arm64_cross_module_abi_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'macos-arm64 preset has 64-bit pointers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/arm64_cross_module_abi_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cortex-m4 has 32-bit pointers (contrast)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/arm64_cross_module_abi_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'arm64 and cortex-m4 pointer widths differ' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
