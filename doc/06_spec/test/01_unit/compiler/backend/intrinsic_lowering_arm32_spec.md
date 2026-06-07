# Intrinsic Lowering Arm32 Specification

> <details>

<!-- sdn-diagram:id=intrinsic_lowering_arm32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=intrinsic_lowering_arm32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

intrinsic_lowering_arm32_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=intrinsic_lowering_arm32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Intrinsic Lowering Arm32 Specification

## Scenarios

### ARM32 lowering — permanently unavailable idioms

#### Sha512Rounds2 is permanently unavailable on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.Sha512Rounds2)).to_equal(true)
```

</details>

#### Sha512Msg1 is permanently unavailable on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.Sha512Msg1)).to_equal(true)
```

</details>

#### Sha512Msg2 is permanently unavailable on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.Sha512Msg2)).to_equal(true)
```

</details>

#### SimdI32x8 is permanently unavailable on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.SimdI32x8)).to_equal(true)
```

</details>

#### SimdF32x8 is permanently unavailable on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.SimdF32x8)).to_equal(true)
```

</details>

#### Crc32U64 is permanently unavailable on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.Crc32U64)).to_equal(true)
```

</details>

#### ClmulLo is permanently unavailable on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.ClmulLo)).to_equal(true)
```

</details>

#### ClmulHi is permanently unavailable on ARM32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.ClmulHi)).to_equal(true)
```

</details>

#### RotateLeft is NOT permanently unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.RotateLeft)).to_equal(false)
```

</details>

#### AesEnc is NOT permanently unavailable (optional extension exists)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.AesEnc)).to_equal(false)
```

</details>

#### SimdI32x4 is NOT permanently unavailable (NEON provides it)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_permanently_unavailable(TargetIdiom.SimdI32x4)).to_equal(false)
```

</details>

### ARM32 lowering — Cortex-M0 baseline decisions

#### RotateLeft is lowered natively on Cortex-M0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.RotateLeft)
expect(d.lowered).to_equal(true)
expect(d.fallback).to_equal(false)
```

</details>

#### ByteSwap is lowered natively on Cortex-M0 (REV instruction)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.ByteSwap)
expect(d.lowered).to_equal(true)
```

</details>

#### AesEnc falls back on Cortex-M0 (no AES extension)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.AesEnc)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
expect(d.reason.len()).to_be_greater_than(0)
```

</details>

#### SimdI32x4 falls back on Cortex-M0 (no NEON)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.SimdI32x4)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### Sha512Rounds2 falls back with permanent unavailability reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.Sha512Rounds2)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

### ARM32 lowering — neon+crypto triple decisions

#### AesEnc is lowered natively with AES extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.AesEnc)
expect(d.lowered).to_equal(true)
expect(d.fallback).to_equal(false)
```

</details>

#### Sha256Rounds2 is lowered natively with SHA2 extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.Sha256Rounds2)
expect(d.lowered).to_equal(true)
```

</details>

#### SimdI32x4 is lowered natively with NEON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.SimdI32x4)
expect(d.lowered).to_equal(true)
```

</details>

#### Sha512Rounds2 still falls back even with full crypto (permanent limit)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.Sha512Rounds2)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### SimdI32x8 still falls back (no 256-bit NEON on ARM32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.SimdI32x8)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

### ARM32 lowering — scalar narrow-form helpers

#### CLZ is always available

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_clz_available()).to_equal(true)
```

</details>

#### RBIT is always available (ARMv6T2+)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_rbit_available()).to_equal(true)
```

</details>

#### REV is always available (ARMv6+)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_rev_available()).to_equal(true)
```

</details>

#### ROL 1 via ROR is 31 (32 - 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_rotate_left_via_ror(1)).to_equal(31)
```

</details>

#### ROL 8 via ROR is 24 (32 - 8)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_rotate_left_via_ror(8)).to_equal(24)
```

</details>

#### ROL 32 via ROR is 0 (identity)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm32_rotate_left_via_ror(32)).to_equal(0)
```

</details>

### RV32 lowering — scalar narrow-form hooks

#### rv32 without Zbb has no native popcount

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac")
expect(rv32_popcount_native(caps)).to_equal(false)
```

</details>

#### rv32 with Zbb has native popcount

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_popcount_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb has native CLZ

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_clz_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb has native CTZ

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_ctz_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb has native byte-swap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_bswap_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb but not Zbkb does not have native bit-reverse

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_bitrev_native(caps)).to_equal(false)
```

</details>

#### rv32 with Zbb+Zbkb has native bit-reverse

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb_zbkb")
expect(rv32_bitrev_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb has native rotate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_rotate_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zkne has native AES encrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zkne")
expect(rv32_aes_enc_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zknd has native AES decrypt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zknd")
expect(rv32_aes_dec_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zknh has native SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zknh")
expect(rv32_sha256_native(caps)).to_equal(true)
```

</details>

#### rv32 baseline has no native AES

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac")
expect(rv32_aes_enc_native(caps)).to_equal(false)
expect(rv32_aes_dec_native(caps)).to_equal(false)
```

</details>

### RV32 lowering — decision predicates

#### SHA-512 is always a fallback on RV32

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zknd_zkne_zknh")
val d = rv32_lowering_decision(caps, TargetIdiom.Sha512Rounds2)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
expect(d.reason.len()).to_be_greater_than(0)
```

</details>

#### CRC32 is always a fallback on RV32 (no hardware CRC in RISC-V)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac")
val d = rv32_lowering_decision(caps, TargetIdiom.Crc32U32)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### ClmulLo is a fallback on RV32 (Zbc not guaranteed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac")
val d = rv32_lowering_decision(caps, TargetIdiom.ClmulLo)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### SimdI32x8 is always a fallback on RV32

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
val d = rv32_lowering_decision(caps, TargetIdiom.SimdI32x8)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### RotateLeft is natively lowered with Zbb

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zbb")
val d = rv32_lowering_decision(caps, TargetIdiom.RotateLeft)
expect(d.lowered).to_equal(true)
expect(d.fallback).to_equal(false)
```

</details>

#### AesEnc is natively lowered with Zkne

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac_zkne")
val d = rv32_lowering_decision(caps, TargetIdiom.AesEnc)
expect(d.lowered).to_equal(true)
expect(d.fallback).to_equal(false)
```

</details>

#### AesEnc falls back without Zkne

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val caps = rv32_caps_from_target("riscv32imac")
val d = rv32_lowering_decision(caps, TargetIdiom.AesEnc)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
expect(d.reason.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/intrinsic_lowering_arm32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ARM32 lowering — permanently unavailable idioms
- ARM32 lowering — Cortex-M0 baseline decisions
- ARM32 lowering — neon+crypto triple decisions
- ARM32 lowering — scalar narrow-form helpers
- RV32 lowering — scalar narrow-form hooks
- RV32 lowering — decision predicates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
