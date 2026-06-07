# Portable Simd Fp Specification

> <details>

<!-- sdn-diagram:id=portable_simd_fp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=portable_simd_fp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

portable_simd_fp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=portable_simd_fp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Portable Simd Fp Specification

## Scenarios

### NumericCaps

#### scalar_only

#### has no vectorization

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = NumericCaps.scalar_only("riscv32", 32)
expect(c.supports_vectorization() == false).to_equal(true)
```

</details>

#### max_simd_bits is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = NumericCaps.scalar_only("riscv32", 32)
expect(c.max_simd_bits()).to_equal(0)
```

</details>

#### pointer_bits is preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = NumericCaps.scalar_only("riscv32", 32)
expect(c.pointer_bits).to_equal(32)
```

</details>

#### x86_64_baseline

#### supports vectorization via simd_128

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = NumericCaps.x86_64_baseline()
expect(c.supports_vectorization()).to_equal(true)
```

</details>

#### max_simd_bits is 128 when only sse2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = NumericCaps.x86_64_baseline()
expect(c.max_simd_bits()).to_equal(128)
```

</details>

#### describe includes hw-fp

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = NumericCaps.x86_64_baseline()
val d = c.describe()
expect(d).to_equal("x86_64 ptr=64b hw-fp simd-128")
```

</details>

### TargetFamily

#### x86_64 arch maps to x86_64 family

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = family_from_arch("x86_64")
expect(f == TargetFamily.x86_64).to_equal(true)
```

</details>

#### riscv32 arch maps to riscv32 family

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = family_from_arch("riscv32")
expect(f == TargetFamily.riscv32).to_equal(true)
```

</details>

#### unknown arch maps to unknown family

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = family_from_arch("mips")
expect(f == TargetFamily.unknown).to_equal(true)
```

</details>

### CapRegistryEntry

#### linux_x86_64

#### has simd_needs_probe true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = TargetSpec.linux_x86_64()
val entry = CapRegistryEntry.derive(spec)
expect(entry.simd_needs_probe).to_equal(true)
```

</details>

#### has simd_128 true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = TargetSpec.linux_x86_64()
val entry = CapRegistryEntry.derive(spec)
expect(entry.has_simd_128).to_equal(true)
```

</details>

#### is_ok is false due to probe diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = TargetSpec.linux_x86_64()
val entry = CapRegistryEntry.derive(spec)
expect(entry.is_ok() == false).to_equal(true)
```

</details>

#### riscv32_baremetal

#### has no simd_128

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = TargetSpec.riscv32_baremetal()
val entry = CapRegistryEntry.derive(spec)
expect(entry.has_simd_128 == false).to_equal(true)
```

</details>

#### is_ok is false for integer-only riscv

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = TargetSpec.riscv32_baremetal()
val entry = CapRegistryEntry.derive(spec)
expect(entry.is_ok() == false).to_equal(true)
```

</details>

### LoweringSelection

#### x86_64 with simd and probe selects x86_sse2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = LoweringConfig.all_enabled()
val sel = LoweringSelection.select("x86_64", true, true, true, cfg)
expect(sel.family_name()).to_equal("x86_sse2")
```

</details>

#### x86_64 with simd and no probe selects x86_avx

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = LoweringConfig.all_enabled()
val sel = LoweringSelection.select("x86_64", true, true, false, cfg)
expect(sel.family_name()).to_equal("x86_avx")
```

</details>

#### riscv64 with fp only selects riscv_fd

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = LoweringConfig.all_enabled()
val sel = LoweringSelection.select("riscv64", true, false, false, cfg)
expect(sel.family_name()).to_equal("riscv_fd")
```

</details>

#### scalar_only config disables vector_simd

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = LoweringConfig.scalar_only()
val sel = LoweringSelection.select("x86_64", true, true, false, cfg)
expect(sel.vector_simd_active == false).to_equal(true)
```

</details>

#### missing simd emits fallback diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = LoweringConfig.all_enabled()
val sel = LoweringSelection.select("riscv32", false, false, false, cfg)
expect(sel.is_ok() == false).to_equal(true)
```

</details>

### FpProfile

#### x86_64 profile tier is hard_fp_simd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fp = FpProfile.for_x86_64()
expect(fp.tier_name()).to_equal("hard-fp-simd")
```

</details>

#### riscv64 fd profile has fma

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fp = FpProfile.for_riscv64_fd()
expect(fp.has_fma).to_equal(true)
```

</details>

#### riscv32 integer profile has no fp

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fp = FpProfile.for_riscv32_int()
expect(fp.has_any_fp() == false).to_equal(true)
```

</details>

#### riscv64 fd describe includes dp=64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fp = FpProfile.for_riscv64_fd()
val d = fp.describe()
expect(d).to_equal("riscv64 fp=hard-fp-dp sp=64 dp=64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/simd/portable_simd_fp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NumericCaps
- TargetFamily
- CapRegistryEntry
- LoweringSelection
- FpProfile

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
