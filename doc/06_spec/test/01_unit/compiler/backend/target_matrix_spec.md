# Target Matrix Specification

> <details>

<!-- sdn-diagram:id=target_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=target_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

target_matrix_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=target_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 74 | 74 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Matrix Specification

## Scenarios

### TargetMatrix — all_target_family_rows

#### returns exactly 6 rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = all_target_family_rows()
expect(rows.len()).to_equal(6)
```

</details>

#### first row is x86-64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = all_target_family_rows()
expect(rows.get(0).name).to_equal("x86-64")
```

</details>

#### second row is x86-32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = all_target_family_rows()
expect(rows.get(1).name).to_equal("x86-32")
```

</details>

#### third row is aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = all_target_family_rows()
expect(rows.get(2).name).to_equal("aarch64")
```

</details>

#### fourth row is arm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = all_target_family_rows()
expect(rows.get(3).name).to_equal("arm32")
```

</details>

#### fifth row is rv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = all_target_family_rows()
expect(rows.get(4).name).to_equal("rv64")
```

</details>

#### sixth row is rv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = all_target_family_rows()
expect(rows.get(5).name).to_equal("rv32")
```

</details>

### TargetMatrix — pointer_bits

#### x86-64 has 64-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_64()
expect(row.pointer_bits).to_equal(64)
```

</details>

#### x86-32 has 32-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_32()
expect(row.pointer_bits).to_equal(32)
```

</details>

#### aarch64 has 64-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_aarch64()
expect(row.pointer_bits).to_equal(64)
```

</details>

#### arm32 has 32-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_arm32()
expect(row.pointer_bits).to_equal(32)
```

</details>

#### rv64 has 64-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_rv64()
expect(row.pointer_bits).to_equal(64)
```

</details>

#### rv32 has 32-bit pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_rv32()
expect(row.pointer_bits).to_equal(32)
```

</details>

### TargetMatrix — x86-64 enable matrix

#### x86-64 enables FixedWidthSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_64()
expect(target_family_row_supports_class(row, TargetFeatureClass.FixedWidthSimd)).to_equal(true)
```

</details>

#### x86-64 enables ScalableSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_64()
expect(target_family_row_supports_class(row, TargetFeatureClass.ScalableSimd)).to_equal(true)
```

</details>

#### x86-64 enables BitManip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_64()
expect(target_family_row_supports_class(row, TargetFeatureClass.BitManip)).to_equal(true)
```

</details>

#### x86-64 enables Crypto

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_64()
expect(target_family_row_supports_class(row, TargetFeatureClass.Crypto)).to_equal(true)
```

</details>

<details>
<summary>Advanced: x86-64 enables Matrix</summary>

#### x86-64 enables Matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_64()
expect(target_family_row_supports_class(row, TargetFeatureClass.Matrix)).to_equal(true)
```

</details>


</details>

### TargetMatrix — x86-32 enable matrix

#### x86-32 enables FixedWidthSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_32()
expect(target_family_row_supports_class(row, TargetFeatureClass.FixedWidthSimd)).to_equal(true)
```

</details>

#### x86-32 disables ScalableSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_32()
expect(target_family_row_supports_class(row, TargetFeatureClass.ScalableSimd)).to_equal(false)
```

</details>

#### x86-32 disables ScalableSimd with non-empty reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_32()
val reason = target_family_row_disabled_reason(row, TargetFeatureClass.ScalableSimd)
expect(reason.len()).to_be_greater_than(0)
```

</details>

<details>
<summary>Advanced: x86-32 disables Matrix with non-empty reason</summary>

#### x86-32 disables Matrix with non-empty reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_x86_32()
expect(target_family_row_supports_class(row, TargetFeatureClass.Matrix)).to_equal(false)
val reason = target_family_row_disabled_reason(row, TargetFeatureClass.Matrix)
expect(reason.len()).to_be_greater_than(0)
```

</details>


</details>

### TargetMatrix — arm32 enable matrix

#### arm32 enables FixedWidthSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_arm32()
expect(target_family_row_supports_class(row, TargetFeatureClass.FixedWidthSimd)).to_equal(true)
```

</details>

#### arm32 disables ScalableSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_arm32()
expect(target_family_row_supports_class(row, TargetFeatureClass.ScalableSimd)).to_equal(false)
```

</details>

<details>
<summary>Advanced: arm32 disables Matrix</summary>

#### arm32 disables Matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_arm32()
expect(target_family_row_supports_class(row, TargetFeatureClass.Matrix)).to_equal(false)
```

</details>


</details>

#### arm32 ScalableSimd disabled reason is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_arm32()
val reason = target_family_row_disabled_reason(row, TargetFeatureClass.ScalableSimd)
expect(reason.len()).to_be_greater_than(0)
```

</details>

### TargetMatrix — rv32 enable matrix

#### rv32 disables FixedWidthSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_rv32()
expect(target_family_row_supports_class(row, TargetFeatureClass.FixedWidthSimd)).to_equal(false)
```

</details>

#### rv32 disables ScalableSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_rv32()
expect(target_family_row_supports_class(row, TargetFeatureClass.ScalableSimd)).to_equal(false)
```

</details>

#### rv32 enables BitManip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_rv32()
expect(target_family_row_supports_class(row, TargetFeatureClass.BitManip)).to_equal(true)
```

</details>

#### rv32 enables Crypto

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_rv32()
expect(target_family_row_supports_class(row, TargetFeatureClass.Crypto)).to_equal(true)
```

</details>

#### rv32 FixedWidthSimd disabled reason is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row = target_family_row_rv32()
val reason = target_family_row_disabled_reason(row, TargetFeatureClass.FixedWidthSimd)
expect(reason.len()).to_be_greater_than(0)
```

</details>

### TargetMatrix — caps_kind_from_triple new arch dispatch

#### i686 prefix dispatches to X86_32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = caps_kind_from_triple("i686")
expect(caps_kind_target_name(kind)).to_equal("x86_32")
```

</details>

#### i386 prefix dispatches to X86_32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = caps_kind_from_triple("i386-unknown-linux-gnu")
expect(caps_kind_target_name(kind)).to_equal("x86_32")
```

</details>

#### thumbv7em prefix dispatches to Arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = caps_kind_from_triple("thumbv7em-none-eabihf")
expect(caps_kind_target_name(kind)).to_equal("arm32")
```

</details>

#### thumbv6m prefix dispatches to Arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = caps_kind_from_triple("thumbv6m-none-eabi")
expect(caps_kind_target_name(kind)).to_equal("arm32")
```

</details>

#### riscv32 prefix dispatches to Rv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = caps_kind_from_triple("riscv32imac-unknown-none-elf")
expect(caps_kind_target_name(kind)).to_equal("riscv32")
```

</details>

#### rv32 prefix dispatches to Rv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = caps_kind_from_triple("rv32imac")
expect(caps_kind_target_name(kind)).to_equal("riscv32")
```

</details>

#### x86_64 prefix still dispatches to x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = caps_kind_from_triple("x86_64-unknown-linux-gnu")
expect(caps_kind_target_name(kind)).to_equal("x86_64")
```

</details>

### TargetMatrix — ArmCaps conservative feature tables

#### thumbv6m baseline has no NEON, no AES, no SHA2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
expect(caps.has_neon).to_equal(false)
expect(caps.has_aes).to_equal(false)
expect(caps.has_sha2).to_equal(false)
```

</details>

#### thumbv7em has DSP but no NEON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv7em-none-eabihf")
expect(caps.has_neon).to_equal(false)
expect(caps.has_dsp).to_equal(true)
```

</details>

#### thumbv7em-neon has NEON but no crypto

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv7em-neon-eabihf")
expect(caps.has_neon).to_equal(true)
expect(caps.has_aes).to_equal(false)
```

</details>

#### neon+crypto triple has NEON + AES + SHA2 + CRC32

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
expect(caps.has_neon).to_equal(true)
expect(caps.has_aes).to_equal(true)
expect(caps.has_sha2).to_equal(true)
expect(caps.has_crc32).to_equal(true)
```

</details>

#### ARM32 RotateLeft is always supported (barrel shifter)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
expect(caps.supports(TargetIdiom.RotateLeft)).to_equal(true)
```

</details>

#### ARM32 CountLeadingZeros is always supported (CLZ from ARMv5)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
expect(caps.supports(TargetIdiom.CountLeadingZeros)).to_equal(true)
```

</details>

#### ARM32 CRC32U64 is always unsupported (64-bit operand unavailable)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
expect(caps.supports(TargetIdiom.Crc32U64)).to_equal(false)
```

</details>

#### ARM32 SimdI32x8 is always unsupported (no 256-bit NEON)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
expect(caps.supports(TargetIdiom.SimdI32x8)).to_equal(false)
```

</details>

#### ARM32 preferred_vector_width is 128 with NEON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
expect(preferred_lane_count_arm(caps, 32)).to_equal(4)
```

</details>

#### ARM32 preferred_vector_width is 32 without NEON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
expect(preferred_lane_count_arm(caps, 32)).to_equal(1)
```

</details>

### TargetMatrix — arm_supports_feature_class

#### neon+crypto supports FixedWidthSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
expect(arm_supports_feature_class(caps, TargetFeatureClass.FixedWidthSimd)).to_equal(true)
```

</details>

#### arm32 never supports ScalableSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
expect(arm_supports_feature_class(caps, TargetFeatureClass.ScalableSimd)).to_equal(false)
```

</details>

#### arm32 always supports BitManip class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
expect(arm_supports_feature_class(caps, TargetFeatureClass.BitManip)).to_equal(true)
```

</details>

### TargetMatrix — Rv32Caps conservative feature tables

#### riscv32imac baseline has no Zbb, no crypto

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac")
expect(caps.has_zbb).to_equal(false)
expect(caps.has_zkne).to_equal(false)
expect(caps.has_zknd).to_equal(false)
expect(caps.has_zknh).to_equal(false)
```

</details>

#### riscv32imac_zbb has Zbb bitmanip

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(caps.has_zbb).to_equal(true)
```

</details>

#### riscv32imac_zbb supports RotateLeft

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(caps.supports(TargetIdiom.RotateLeft)).to_equal(true)
```

</details>

#### riscv32imac_zknd_zkne_zknh supports AesEnc and SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zknd_zkne_zknh")
expect(caps.supports(TargetIdiom.AesEnc)).to_equal(true)
expect(caps.supports(TargetIdiom.Sha256Rounds2)).to_equal(true)
```

</details>

#### rv32 Sha512Rounds2 is always unsupported (64-bit ops unavailable)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zknd_zkne_zknh")
expect(caps.supports(TargetIdiom.Sha512Rounds2)).to_equal(false)
```

</details>

#### rv32 SimdI32x8 is always unsupported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(caps.supports(TargetIdiom.SimdI32x8)).to_equal(false)
```

</details>

#### rv32 preferred vector width is 32 without V

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac")
expect(preferred_lane_count_rv32(caps, 32)).to_equal(1)
```

</details>

### TargetMatrix — rv32_supports_feature_class

#### riscv32imac_zbb supports BitManip class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_supports_feature_class(caps, TargetFeatureClass.BitManip)).to_equal(true)
```

</details>

#### rv32 never supports ScalableSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_supports_feature_class(caps, TargetFeatureClass.ScalableSimd)).to_equal(false)
```

</details>

#### riscv32imac_zknd_zkne supports Crypto class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zknd_zkne")
expect(rv32_supports_feature_class(caps, TargetFeatureClass.Crypto)).to_equal(true)
```

</details>

#### rv32 baseline does not support Crypto class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac")
expect(rv32_supports_feature_class(caps, TargetFeatureClass.Crypto)).to_equal(false)
```

</details>

### TargetMatrix — X86_32Caps feature tables

#### i686 baseline has SSE2 but no SSE42, no crypto

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-linux-gnu")
expect(caps.has_sse2).to_equal(true)
expect(caps.has_sse42).to_equal(false)
expect(caps.has_aes).to_equal(false)
```

</details>

#### i686-v2 has SSE42 and POPCNT but no AES

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-v2")
expect(caps.has_sse42).to_equal(true)
expect(caps.has_popcnt).to_equal(true)
expect(caps.has_aes).to_equal(false)
```

</details>

#### i686-v3 has AES, PCLMUL, AVX, SHA-NI

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-v3")
expect(caps.has_aes).to_equal(true)
expect(caps.has_pclmul).to_equal(true)
expect(caps.has_avx).to_equal(true)
expect(caps.has_sha_ni).to_equal(true)
```

</details>

#### x86-32 CRC32U64 always unsupported (64-bit dst unavailable in 32-bit mode)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-v3")
expect(caps.supports(TargetIdiom.Crc32U64)).to_equal(false)
```

</details>

#### x86-32 RotateLeft always supported

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-linux-gnu")
expect(caps.supports(TargetIdiom.RotateLeft)).to_equal(true)
```

</details>

#### x86-32 ByteSwap always supported (BSWAP r32 from 486+)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-linux-gnu")
expect(caps.supports(TargetIdiom.ByteSwap)).to_equal(true)
```

</details>

#### x86-32 SimdI32x4 supported with SSE2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-linux-gnu")
expect(caps.supports(TargetIdiom.SimdI32x4)).to_equal(true)
```

</details>

#### x86-32 preferred_vector_width is 4 lanes for f32 with AVX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-v3")
expect(preferred_lane_count_x86_32(caps, 32)).to_equal(8)
```

</details>

#### x86-32 preferred_vector_width is 4 lanes for f32 without AVX

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-linux-gnu")
expect(preferred_lane_count_x86_32(caps, 32)).to_equal(4)
```

</details>

### TargetMatrix — x86_32_supports_feature_class

#### i686-v3 supports Crypto class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-v3")
expect(x86_32_supports_feature_class(caps, TargetFeatureClass.Crypto)).to_equal(true)
```

</details>

#### x86-32 never supports ScalableSimd

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-v3")
expect(x86_32_supports_feature_class(caps, TargetFeatureClass.ScalableSimd)).to_equal(false)
```

</details>

#### i686-v2 supports BitManip class (SSE4.2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = x86_32_caps_from_target("i686-v2")
expect(x86_32_supports_feature_class(caps, TargetFeatureClass.BitManip)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/target_matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TargetMatrix — all_target_family_rows
- TargetMatrix — pointer_bits
- TargetMatrix — x86-64 enable matrix
- TargetMatrix — x86-32 enable matrix
- TargetMatrix — arm32 enable matrix
- TargetMatrix — rv32 enable matrix
- TargetMatrix — caps_kind_from_triple new arch dispatch
- TargetMatrix — ArmCaps conservative feature tables
- TargetMatrix — arm_supports_feature_class
- TargetMatrix — Rv32Caps conservative feature tables
- TargetMatrix — rv32_supports_feature_class
- TargetMatrix — X86_32Caps feature tables
- TargetMatrix — x86_32_supports_feature_class

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 74 |
| Active scenarios | 74 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
