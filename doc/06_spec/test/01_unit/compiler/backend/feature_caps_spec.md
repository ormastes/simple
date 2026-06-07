# Feature Caps Specification

> <details>

<!-- sdn-diagram:id=feature_caps_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feature_caps_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feature_caps_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feature_caps_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Feature Caps Specification

## Scenarios

### TargetCaps — x86_64 preset derivation

#### x86_64-v1 has none of aes/sha/sse42/popcnt/pclmul/avx2/avx512

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v1")
expect(caps.has_aes).to_equal(false)
expect(caps.has_sha_ni).to_equal(false)
expect(caps.has_sse42).to_equal(false)
expect(caps.has_popcnt).to_equal(false)
expect(caps.has_pclmul).to_equal(false)
expect(caps.has_avx2).to_equal(false)
expect(caps.has_avx512).to_equal(false)
```

</details>

#### x86_64-v2 has sse42 + popcnt only (no aes, no pclmul, no avx2, no avx512, no sha_ni)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v2")
expect(caps.has_sse42).to_equal(true)
expect(caps.has_popcnt).to_equal(true)
expect(caps.has_aes).to_equal(false)
expect(caps.has_sha_ni).to_equal(false)
expect(caps.has_pclmul).to_equal(false)
expect(caps.has_avx2).to_equal(false)
expect(caps.has_avx512).to_equal(false)
```

</details>

#### x86_64-v3 has aes + pclmul + avx2 + sse42, no avx512, no sha_ni

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v3")
expect(caps.has_aes).to_equal(true)
expect(caps.has_sse42).to_equal(true)
expect(caps.has_popcnt).to_equal(true)
expect(caps.has_pclmul).to_equal(true)
expect(caps.has_avx2).to_equal(true)
expect(caps.has_sha_ni).to_equal(false)
expect(caps.has_avx512).to_equal(false)
```

</details>

#### x86_64-v4 has avx512 + sha_ni in addition to v3 features

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v4")
expect(caps.has_aes).to_equal(true)
expect(caps.has_sha_ni).to_equal(true)
expect(caps.has_sse42).to_equal(true)
expect(caps.has_popcnt).to_equal(true)
expect(caps.has_pclmul).to_equal(true)
expect(caps.has_avx2).to_equal(true)
expect(caps.has_avx512).to_equal(true)
```

</details>

#### unknown triple defaults to all-false

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("unknown-triple-xyz")
expect(caps.has_aes).to_equal(false)
expect(caps.has_sha_ni).to_equal(false)
expect(caps.has_sse42).to_equal(false)
expect(caps.has_popcnt).to_equal(false)
expect(caps.has_pclmul).to_equal(false)
expect(caps.has_avx2).to_equal(false)
expect(caps.has_avx512).to_equal(false)
```

</details>

### TargetCaps — supports() dispatch

#### X86Caps with has_aes=true supports AesEnc

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = X86Caps(
    has_aes: true,
    has_sha_ni: false,
    has_sse42: false,
    has_popcnt: false,
    has_pclmul: false,
    has_avx: false,
    has_avx2: false,
    has_avx512: false,
    has_bmi1: false
)
expect(caps.supports(TargetIdiom.AesEnc)).to_equal(true)
```

</details>

#### X86Caps with has_aes=false reports false for AesEnc

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = X86Caps(
    has_aes: false,
    has_sha_ni: false,
    has_sse42: false,
    has_popcnt: false,
    has_pclmul: false,
    has_avx: false,
    has_avx2: false,
    has_avx512: false,
    has_bmi1: false
)
expect(caps.supports(TargetIdiom.AesEnc)).to_equal(false)
```

</details>

#### X86Caps supports ByteSwap without sse42

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = X86Caps(
    has_aes: false,
    has_sha_ni: false,
    has_sse42: false,
    has_popcnt: false,
    has_pclmul: false,
    has_avx: false,
    has_avx2: false,
    has_avx512: false,
    has_bmi1: false
)
expect(caps.supports(TargetIdiom.ByteSwap)).to_equal(true)
```

</details>

#### X86Caps with sse42/popcnt but no bmi1 blocks CountLeadingZeros and CountTrailingZeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = X86Caps(
    has_aes: false,
    has_sha_ni: false,
    has_sse42: true,
    has_popcnt: true,
    has_pclmul: false,
    has_avx: false,
    has_avx2: false,
    has_avx512: false,
    has_bmi1: false
)
expect(caps.supports(TargetIdiom.CountLeadingZeros)).to_equal(false)
expect(caps.supports(TargetIdiom.CountTrailingZeros)).to_equal(false)
```

</details>

#### Aarch64Caps with has_aes=true supports AesEnc

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = Aarch64Caps(
    has_aes: true,
    has_sha2: false,
    has_sha3: false,
    has_crc32: false,
    has_pmull: false,
    has_sve2: false,
    has_neon: true,
    has_sha512: false
)
expect(caps.supports(TargetIdiom.AesEnc)).to_equal(true)
```

</details>

#### Rv64Caps with has_zvkned=true supports AesEnc

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = Rv64Caps(
    has_zvkned: true,
    has_zvknh: false,
    has_zvkg: false,
    has_zbb: false,
    has_zbkb: false,
    has_v: true,
    vlen_bits: 128
)
expect(caps.supports(TargetIdiom.AesEnc)).to_equal(true)
```

</details>

#### Rv64Caps with zbb but no v supports Popcount

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = Rv64Caps(
    has_zvkned: false,
    has_zvknh: false,
    has_zvkg: false,
    has_zbb: true,
    has_zbkb: false,
    has_v: false,
    vlen_bits: 128
)
expect(caps.supports(TargetIdiom.Popcount)).to_equal(true)
```

</details>

#### Rv64Caps with zbkb but no zbb supports RotateLeft

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = Rv64Caps(
    has_zvkned: false,
    has_zvknh: false,
    has_zvkg: false,
    has_zbb: false,
    has_zbkb: true,
    has_v: false,
    vlen_bits: 128
)
expect(caps.supports(TargetIdiom.RotateLeft)).to_equal(true)
```

</details>

#### Rv64Caps needs both zbb and zbkb for BitReverse

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = Rv64Caps(
    has_zvkned: false,
    has_zvknh: false,
    has_zvkg: false,
    has_zbb: true,
    has_zbkb: false,
    has_v: false,
    vlen_bits: 128
)
expect(caps.supports(TargetIdiom.BitReverse)).to_equal(false)
```

</details>

#### cost(unsupported idiom) returns -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = X86Caps(
    has_aes: false,
    has_sha_ni: false,
    has_sse42: false,
    has_popcnt: false,
    has_pclmul: false,
    has_avx: false,
    has_avx2: false,
    has_avx512: false,
    has_bmi1: false
)
expect(caps.cost(TargetIdiom.AesEnc)).to_equal(-1)
```

</details>

### TargetCaps — preferred_vector_width_bits

#### X86Caps avx512 returns 512

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v4")
expect(caps.preferred_vector_width_bits() > 0).to_equal(true)
expect(caps.preferred_vector_width_bits()).to_equal(512)
```

</details>

#### X86Caps avx2-only returns 256

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v3")
expect(caps.preferred_vector_width_bits()).to_equal(256)
```

</details>

#### X86Caps baseline returns 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v1")
expect(caps.preferred_vector_width_bits()).to_equal(128)
```

</details>

### TargetCaps — feature-class helpers

<details>
<summary>Advanced: MatrixDot is classified as Matrix</summary>

#### MatrixDot is classified as Matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(idiom_feature_class(TargetIdiom.MatrixDot)).to_equal(TargetFeatureClass.Matrix)
```

</details>


</details>

#### RotateLeft is classified as BitManip

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(idiom_feature_class(TargetIdiom.RotateLeft)).to_equal(TargetFeatureClass.BitManip)
```

</details>

#### x86 v3 supports scalable-simd planning class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v3")
expect(x86_supports_feature_class(caps, TargetFeatureClass.ScalableSimd)).to_equal(true)
```

</details>

#### aarch64 neon-only supports fixed-width simd but not scalable-simd

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = aarch64_caps_from_target("aarch64")
expect(aarch64_supports_feature_class(caps, TargetFeatureClass.FixedWidthSimd)).to_equal(true)
expect(aarch64_supports_feature_class(caps, TargetFeatureClass.ScalableSimd)).to_equal(false)
```

</details>

<details>
<summary>Advanced: rv64gcv supports matrix class when V is present</summary>

#### rv64gcv supports matrix class when V is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv64_caps_from_target("rv64gcv")
expect(rv64_supports_feature_class(caps, TargetFeatureClass.Matrix)).to_equal(true)
```

</details>


</details>

#### rv64gc_zbb supports bitmanip class without V

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv64_caps_from_target("rv64gc_zbb")
expect(rv64_supports_feature_class(caps, TargetFeatureClass.BitManip)).to_equal(true)
expect(rv64_supports_feature_class(caps, TargetFeatureClass.Matrix)).to_equal(false)
```

</details>

### TargetCaps — preferred lane count helpers

#### x86 v3 prefers 8 lanes for f32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_caps_from_target("x86_64-v3")
expect(preferred_lane_count_x86(caps, 32)).to_equal(8)
```

</details>

#### aarch64 neon prefers 4 lanes for f32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = aarch64_caps_from_target("aarch64")
expect(preferred_lane_count_aarch64(caps, 32)).to_equal(4)
```

</details>

#### rv64gcv_v256 prefers 8 lanes for f32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv64_caps_from_target("rv64gcv_v256")
expect(preferred_lane_count_rv64(caps, 32)).to_equal(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/feature_caps_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TargetCaps — x86_64 preset derivation
- TargetCaps — supports() dispatch
- TargetCaps — preferred_vector_width_bits
- TargetCaps — feature-class helpers
- TargetCaps — preferred lane count helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
