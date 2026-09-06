# feature_caps_spec

> Purpose: Prove that TargetCaps — x86_64 preset derivation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# feature_caps_spec

Purpose: Prove that TargetCaps — x86_64 preset derivation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/feature_caps_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that TargetCaps — x86_64 preset derivation.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### TargetCaps — x86_64 preset derivation

#### x86_64-v1 has none of aes/sha/sse42/popcnt/pclmul/avx2/avx512

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- x86_64-v1 has none of aes/sha/sse42/popcnt/pclmul/avx2/avx512
- Verify: x86_64-v1 has none of aes/sha/sse42/popcnt/pclmul/avx2/avx512
   - Expected: caps.has_aes is false
   - Expected: caps.has_sha_ni is false
   - Expected: caps.has_sse42 is false
   - Expected: caps.has_popcnt is false
   - Expected: caps.has_pclmul is false
   - Expected: caps.has_avx2 is false
   - Expected: caps.has_avx512 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x86_64-v1 has none of aes/sha/sse42/popcnt/pclmul/avx2/avx512")
step("Verify: x86_64-v1 has none of aes/sha/sse42/popcnt/pclmul/avx2/avx512")
# @req: REQ-COMP-TARGETCAPS-X86-64-PRESET-DERIVATION-001
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

- x86_64-v2 has sse42 + popcnt only (no aes, no pclmul, no avx2, no avx512, no sha_ni)
- Verify: x86_64-v2 has sse42 + popcnt only (no aes, no pclmul, no avx2, no avx512, no sha_ni)
   - Expected: caps.has_sse42 is true
   - Expected: caps.has_popcnt is true
   - Expected: caps.has_aes is false
   - Expected: caps.has_sha_ni is false
   - Expected: caps.has_pclmul is false
   - Expected: caps.has_avx2 is false
   - Expected: caps.has_avx512 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x86_64-v2 has sse42 + popcnt only (no aes, no pclmul, no avx2, no avx512, no sha_ni)")
step("Verify: x86_64-v2 has sse42 + popcnt only (no aes, no pclmul, no avx2, no avx512, no sha_ni)")
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

- x86_64-v3 has aes + pclmul + avx2 + sse42, no avx512, no sha_ni
- Verify: x86_64-v3 has aes + pclmul + avx2 + sse42, no avx512, no sha_ni
   - Expected: caps.has_aes is true
   - Expected: caps.has_sse42 is true
   - Expected: caps.has_popcnt is true
   - Expected: caps.has_pclmul is true
   - Expected: caps.has_avx2 is true
   - Expected: caps.has_sha_ni is false
   - Expected: caps.has_avx512 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x86_64-v3 has aes + pclmul + avx2 + sse42, no avx512, no sha_ni")
step("Verify: x86_64-v3 has aes + pclmul + avx2 + sse42, no avx512, no sha_ni")
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

- x86_64-v4 has avx512 + sha_ni in addition to v3 features
- Verify: x86_64-v4 has avx512 + sha_ni in addition to v3 features
   - Expected: caps.has_aes is true
   - Expected: caps.has_sha_ni is true
   - Expected: caps.has_sse42 is true
   - Expected: caps.has_popcnt is true
   - Expected: caps.has_pclmul is true
   - Expected: caps.has_avx2 is true
   - Expected: caps.has_avx512 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x86_64-v4 has avx512 + sha_ni in addition to v3 features")
step("Verify: x86_64-v4 has avx512 + sha_ni in addition to v3 features")
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

- unknown triple defaults to all-false
- Verify: unknown triple defaults to all-false
   - Expected: caps.has_aes is false
   - Expected: caps.has_sha_ni is false
   - Expected: caps.has_sse42 is false
   - Expected: caps.has_popcnt is false
   - Expected: caps.has_pclmul is false
   - Expected: caps.has_avx2 is false
   - Expected: caps.has_avx512 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown triple defaults to all-false")
step("Verify: unknown triple defaults to all-false")
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

- X86Caps with has_aes=true supports AesEnc
- Verify: X86Caps with has_aes=true supports AesEnc
   - Expected: caps.supports(TargetIdiom.AesEnc) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("X86Caps with has_aes=true supports AesEnc")
step("Verify: X86Caps with has_aes=true supports AesEnc")
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

- X86Caps with has_aes=false reports false for AesEnc
- Verify: X86Caps with has_aes=false reports false for AesEnc
   - Expected: caps.supports(TargetIdiom.AesEnc) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("X86Caps with has_aes=false reports false for AesEnc")
step("Verify: X86Caps with has_aes=false reports false for AesEnc")
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

- X86Caps supports ByteSwap without sse42
- Verify: X86Caps supports ByteSwap without sse42
   - Expected: caps.supports(TargetIdiom.ByteSwap) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("X86Caps supports ByteSwap without sse42")
step("Verify: X86Caps supports ByteSwap without sse42")
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

- X86Caps with sse42/popcnt but no bmi1 blocks CountLeadingZeros and CountTrailingZeros
- Verify: X86Caps with sse42/popcnt but no bmi1 blocks CountLeadingZeros and CountTrailingZeros
   - Expected: caps.supports(TargetIdiom.CountLeadingZeros) is false
   - Expected: caps.supports(TargetIdiom.CountTrailingZeros) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("X86Caps with sse42/popcnt but no bmi1 blocks CountLeadingZeros and CountTrailingZeros")
step("Verify: X86Caps with sse42/popcnt but no bmi1 blocks CountLeadingZeros and CountTrailingZeros")
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

- Aarch64Caps with has_aes=true supports AesEnc
- Verify: Aarch64Caps with has_aes=true supports AesEnc
   - Expected: caps.supports(TargetIdiom.AesEnc) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Aarch64Caps with has_aes=true supports AesEnc")
step("Verify: Aarch64Caps with has_aes=true supports AesEnc")
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

- Rv64Caps with has_zvkned=true supports AesEnc
- Verify: Rv64Caps with has_zvkned=true supports AesEnc
   - Expected: caps.supports(TargetIdiom.AesEnc) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Rv64Caps with has_zvkned=true supports AesEnc")
step("Verify: Rv64Caps with has_zvkned=true supports AesEnc")
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

- Rv64Caps with zbb but no v supports Popcount
- Verify: Rv64Caps with zbb but no v supports Popcount
   - Expected: caps.supports(TargetIdiom.Popcount) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Rv64Caps with zbb but no v supports Popcount")
step("Verify: Rv64Caps with zbb but no v supports Popcount")
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

- Rv64Caps with zbkb but no zbb supports RotateLeft
- Verify: Rv64Caps with zbkb but no zbb supports RotateLeft
   - Expected: caps.supports(TargetIdiom.RotateLeft) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Rv64Caps with zbkb but no zbb supports RotateLeft")
step("Verify: Rv64Caps with zbkb but no zbb supports RotateLeft")
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

- Rv64Caps needs both zbb and zbkb for BitReverse
- Verify: Rv64Caps needs both zbb and zbkb for BitReverse
   - Expected: caps.supports(TargetIdiom.BitReverse) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Rv64Caps needs both zbb and zbkb for BitReverse")
step("Verify: Rv64Caps needs both zbb and zbkb for BitReverse")
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

- cost(unsupported idiom) returns -1
- Verify: cost(unsupported idiom) returns -1
   - Expected: caps.cost(TargetIdiom.AesEnc) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("cost(unsupported idiom) returns -1")
step("Verify: cost(unsupported idiom) returns -1")
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

- X86Caps avx512 returns 512
- Verify: X86Caps avx512 returns 512
   - Expected: caps.preferred_vector_width_bits() > 0 is true
   - Expected: caps.preferred_vector_width_bits() equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("X86Caps avx512 returns 512")
step("Verify: X86Caps avx512 returns 512")
val caps = x86_caps_from_target("x86_64-v4")
expect(caps.preferred_vector_width_bits() > 0).to_equal(true)
expect(caps.preferred_vector_width_bits()).to_equal(512)
```

</details>

#### X86Caps avx2-only returns 256

- X86Caps avx2-only returns 256
- Verify: X86Caps avx2-only returns 256
   - Expected: caps.preferred_vector_width_bits() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("X86Caps avx2-only returns 256")
step("Verify: X86Caps avx2-only returns 256")
val caps = x86_caps_from_target("x86_64-v3")
expect(caps.preferred_vector_width_bits()).to_equal(256)
```

</details>

#### X86Caps baseline returns 128

- X86Caps baseline returns 128
- Verify: X86Caps baseline returns 128
   - Expected: caps.preferred_vector_width_bits() equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("X86Caps baseline returns 128")
step("Verify: X86Caps baseline returns 128")
val caps = x86_caps_from_target("x86_64-v1")
expect(caps.preferred_vector_width_bits()).to_equal(128)
```

</details>

### TargetCaps — feature-class helpers

<details>
<summary>Advanced: MatrixDot is classified as Matrix</summary>

#### MatrixDot is classified as Matrix

- MatrixDot is classified as Matrix
- Verify: MatrixDot is classified as Matrix
   - Expected: idiom_feature_class(TargetIdiom.MatrixDot) equals `TargetFeatureClass.Matrix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("MatrixDot is classified as Matrix")
step("Verify: MatrixDot is classified as Matrix")
expect(idiom_feature_class(TargetIdiom.MatrixDot)).to_equal(TargetFeatureClass.Matrix)
```

</details>


</details>

#### RotateLeft is classified as BitManip

- RotateLeft is classified as BitManip
- Verify: RotateLeft is classified as BitManip
   - Expected: idiom_feature_class(TargetIdiom.RotateLeft) equals `TargetFeatureClass.BitManip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("RotateLeft is classified as BitManip")
step("Verify: RotateLeft is classified as BitManip")
expect(idiom_feature_class(TargetIdiom.RotateLeft)).to_equal(TargetFeatureClass.BitManip)
```

</details>

#### x86 v3 supports scalable-simd planning class

- x86 v3 supports scalable-simd planning class
- Verify: x86 v3 supports scalable-simd planning class
   - Expected: x86_supports_feature_class(caps, TargetFeatureClass.ScalableSimd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x86 v3 supports scalable-simd planning class")
step("Verify: x86 v3 supports scalable-simd planning class")
val caps = x86_caps_from_target("x86_64-v3")
expect(x86_supports_feature_class(caps, TargetFeatureClass.ScalableSimd)).to_equal(true)
```

</details>

#### aarch64 neon-only supports fixed-width simd but not scalable-simd

- aarch64 neon-only supports fixed-width simd but not scalable-simd
- Verify: aarch64 neon-only supports fixed-width simd but not scalable-simd
   - Expected: aarch64_supports_feature_class(caps, TargetFeatureClass.FixedWidthSimd) is true
   - Expected: aarch64_supports_feature_class(caps, TargetFeatureClass.ScalableSimd) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("aarch64 neon-only supports fixed-width simd but not scalable-simd")
step("Verify: aarch64 neon-only supports fixed-width simd but not scalable-simd")
val caps = aarch64_caps_from_target("aarch64")
expect(aarch64_supports_feature_class(caps, TargetFeatureClass.FixedWidthSimd)).to_equal(true)
expect(aarch64_supports_feature_class(caps, TargetFeatureClass.ScalableSimd)).to_equal(false)
```

</details>

<details>
<summary>Advanced: rv64gcv supports matrix class when V is present</summary>

#### rv64gcv supports matrix class when V is present

- rv64gcv supports matrix class when V is present
- Verify: rv64gcv supports matrix class when V is present
   - Expected: rv64_supports_feature_class(caps, TargetFeatureClass.Matrix) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rv64gcv supports matrix class when V is present")
step("Verify: rv64gcv supports matrix class when V is present")
val caps = rv64_caps_from_target("rv64gcv")
expect(rv64_supports_feature_class(caps, TargetFeatureClass.Matrix)).to_equal(true)
```

</details>


</details>

#### rv64gc_zbb supports bitmanip class without V

- rv64gc_zbb supports bitmanip class without V
- Verify: rv64gc_zbb supports bitmanip class without V
   - Expected: rv64_supports_feature_class(caps, TargetFeatureClass.BitManip) is true
   - Expected: rv64_supports_feature_class(caps, TargetFeatureClass.Matrix) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rv64gc_zbb supports bitmanip class without V")
step("Verify: rv64gc_zbb supports bitmanip class without V")
val caps = rv64_caps_from_target("rv64gc_zbb")
expect(rv64_supports_feature_class(caps, TargetFeatureClass.BitManip)).to_equal(true)
expect(rv64_supports_feature_class(caps, TargetFeatureClass.Matrix)).to_equal(false)
```

</details>

### TargetCaps — preferred lane count helpers

#### x86 v3 prefers 8 lanes for f32

- x86 v3 prefers 8 lanes for f32
- Verify: x86 v3 prefers 8 lanes for f32
   - Expected: preferred_lane_count_x86(caps, 32) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("x86 v3 prefers 8 lanes for f32")
step("Verify: x86 v3 prefers 8 lanes for f32")
val caps = x86_caps_from_target("x86_64-v3")
expect(preferred_lane_count_x86(caps, 32)).to_equal(8)
```

</details>

#### aarch64 neon prefers 4 lanes for f32

- aarch64 neon prefers 4 lanes for f32
- Verify: aarch64 neon prefers 4 lanes for f32
   - Expected: preferred_lane_count_aarch64(caps, 32) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("aarch64 neon prefers 4 lanes for f32")
step("Verify: aarch64 neon prefers 4 lanes for f32")
val caps = aarch64_caps_from_target("aarch64")
expect(preferred_lane_count_aarch64(caps, 32)).to_equal(4)
```

</details>

#### rv64gcv_v256 prefers 8 lanes for f32

- rv64gcv_v256 prefers 8 lanes for f32
- Verify: rv64gcv_v256 prefers 8 lanes for f32
   - Expected: preferred_lane_count_rv64(caps, 32) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rv64gcv_v256 prefers 8 lanes for f32")
step("Verify: rv64gcv_v256 prefers 8 lanes for f32")
val caps = rv64_caps_from_target("rv64gcv_v256")
expect(preferred_lane_count_rv64(caps, 32)).to_equal(8)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-TARGETCAPS-X86-64-PRESET-DERIVATION-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e777bbbd87a208c4937ee57ac30ecf4b92504572dca0c31ad8fd70b14a7b592`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e777bbbd87a208c4937ee57ac30ecf4b92504572dca0c31ad8fd70b14a7b592`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e777bbbd87a208c4937ee57ac30ecf4b92504572dca0c31ad8fd70b14a7b592`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/feature_caps_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/feature_caps_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/feature_caps_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/feature_caps_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/feature_caps_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/feature_caps_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x86_64-v1 has none of aes/sha/sse42/popcnt/pclmul/avx2/avx512' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/feature_caps_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x86_64-v2 has sse42 + popcnt only (no aes, no pclmul, no avx2, no avx512, no sha_ni)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/feature_caps_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x86_64-v3 has aes + pclmul + avx2 + sse42, no avx512, no sha_ni' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
