# Hal Trait Surface Specification

> <details>

<!-- sdn-diagram:id=hal_trait_surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_trait_surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_trait_surface_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_trait_surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Trait Surface Specification

## Scenarios

### AC-3 — 16 HAL traits declared in arch/hal.spl

#### hal.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(HAL_PATH)).to_equal(true)
```

</details>

#### declares HalConsole (existing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalConsole")).to_equal(true)
```

</details>

#### declares HalBoot (existing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalBoot")).to_equal(true)
```

</details>

#### declares HalCpu (existing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalCpu")).to_equal(true)
```

</details>

#### declares HalPower (existing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalPower")).to_equal(true)
```

</details>

#### declares HalPaging (existing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalPaging")).to_equal(true)
```

</details>

#### declares HalInterrupt (existing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalInterrupt")).to_equal(true)
```

</details>

#### declares HalTimer (existing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalTimer")).to_equal(true)
```

</details>

#### declares HalContext (existing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalContext")).to_equal(true)
```

</details>

#### declares HalEntropy (NEW — R6 canary entropy)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalEntropy")).to_equal(true)
```

</details>

#### declares HalCstart (NEW — replaces simpleos_crt0.S/setjmp.S)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalCstart")).to_equal(true)
```

</details>

#### declares HalSyscall (NEW — capability-checked trampoline)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalSyscall")).to_equal(true)
```

</details>

#### declares HalCanary (NEW — per-boot stack guard)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalCanary")).to_equal(true)
```

</details>

#### declares HalBarrier (NEW — MMIO ordering)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalBarrier")).to_equal(true)
```

</details>

#### declares HalCache (NEW — i/d-cache maintenance)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalCache")).to_equal(true)
```

</details>

#### declares HalSmp (NEW — RESERVED, shape only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalSmp")).to_equal(true)
```

</details>

#### declares HalPerCpu (NEW — RESERVED, shape only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body: text = file_read(HAL_PATH)
expect(body.contains("trait HalPerCpu")).to_equal(true)
```

</details>

### AC-3 — per-arch impls present for 14 implementable traits

#### x86_64 cstart.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/kernel/arch/x86_64/cstart.spl")).to_equal(true)
```

</details>

#### x86_32 cstart.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/kernel/arch/x86_32/cstart.spl")).to_equal(true)
```

</details>

#### arm32 cstart.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/kernel/arch/arm32/cstart.spl")).to_equal(true)
```

</details>

#### arm64 cstart.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/kernel/arch/arm64/cstart.spl")).to_equal(true)
```

</details>

#### riscv32 cstart.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/kernel/arch/riscv32/cstart.spl")).to_equal(true)
```

</details>

#### riscv64 cstart.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/kernel/arch/riscv64/cstart.spl")).to_equal(true)
```

</details>

#### x86_64 entropy.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/kernel/arch/x86_64/entropy.spl")).to_equal(true)
```

</details>

#### arm64 entropy.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/kernel/arch/arm64/entropy.spl")).to_equal(true)
```

</details>

#### riscv64 entropy.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("src/os/kernel/arch/riscv64/entropy.spl")).to_equal(true)
```

</details>

### AC-3 — arch-neutral kernel uses only os.kernel.arch.hal

#### loc report exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(LOC_REPORT)).to_equal(true)
```

</details>

#### report shows zero arch-specific imports outside arch/

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report: text = file_read(LOC_REPORT)
expect(report.contains("\"direct_arch_imports_outside_arch\": 0")).to_equal(true)
```

</details>

### AC-3 — per-arch LoC delta ≥40% (or ≥25% with rationale)

#### loc report contains per-arch delta_pct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report: text = file_read(LOC_REPORT)
expect(report.contains("\"x86_64\"")).to_equal(true)
expect(report.contains("\"delta_pct\"")).to_equal(true)
```

</details>

#### x86_64 delta_pct meets the floor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report: text = file_read(LOC_REPORT)
expect(report.contains("\"x86_64_meets_floor\": true")).to_equal(true)
```

</details>

#### all six archs meet the floor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report: text = file_read(LOC_REPORT)
expect(report.contains("\"all_archs_meet_floor\": true")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/multiarch/hal_trait_surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AC-3 — 16 HAL traits declared in arch/hal.spl
- AC-3 — per-arch impls present for 14 implementable traits
- AC-3 — arch-neutral kernel uses only os.kernel.arch.hal
- AC-3 — per-arch LoC delta ≥40% (or ≥25% with rationale)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
