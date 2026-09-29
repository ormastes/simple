# intrinsic_lowering_arm32_spec

> Purpose: Prove that ARM32 lowering — permanently unavailable idioms.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# intrinsic_lowering_arm32_spec

Purpose: Prove that ARM32 lowering — permanently unavailable idioms.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/intrinsic_lowering_arm32_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that ARM32 lowering — permanently unavailable idioms.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### ARM32 lowering — permanently unavailable idioms

#### Sha512Rounds2 is permanently unavailable on ARM32

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Sha512Rounds2 is permanently unavailable on ARM32
- Verify: Sha512Rounds2 is permanently unavailable on ARM32
   - Expected: arm32_permanently_unavailable(TargetIdiom.Sha512Rounds2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha512Rounds2 is permanently unavailable on ARM32")
step("Verify: Sha512Rounds2 is permanently unavailable on ARM32")
# @req: REQ-COMP-ARM32-LOWERING-PERMANENTLY-UNAVAILABLE-I-001
expect(arm32_permanently_unavailable(TargetIdiom.Sha512Rounds2)).to_equal(true)
```

</details>

#### Sha512Msg1 is permanently unavailable on ARM32

- Sha512Msg1 is permanently unavailable on ARM32
- Verify: Sha512Msg1 is permanently unavailable on ARM32
   - Expected: arm32_permanently_unavailable(TargetIdiom.Sha512Msg1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha512Msg1 is permanently unavailable on ARM32")
step("Verify: Sha512Msg1 is permanently unavailable on ARM32")
expect(arm32_permanently_unavailable(TargetIdiom.Sha512Msg1)).to_equal(true)
```

</details>

#### Sha512Msg2 is permanently unavailable on ARM32

- Sha512Msg2 is permanently unavailable on ARM32
- Verify: Sha512Msg2 is permanently unavailable on ARM32
   - Expected: arm32_permanently_unavailable(TargetIdiom.Sha512Msg2) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha512Msg2 is permanently unavailable on ARM32")
step("Verify: Sha512Msg2 is permanently unavailable on ARM32")
expect(arm32_permanently_unavailable(TargetIdiom.Sha512Msg2)).to_equal(true)
```

</details>

#### SimdI32x8 is permanently unavailable on ARM32

- SimdI32x8 is permanently unavailable on ARM32
- Verify: SimdI32x8 is permanently unavailable on ARM32
   - Expected: arm32_permanently_unavailable(TargetIdiom.SimdI32x8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SimdI32x8 is permanently unavailable on ARM32")
step("Verify: SimdI32x8 is permanently unavailable on ARM32")
expect(arm32_permanently_unavailable(TargetIdiom.SimdI32x8)).to_equal(true)
```

</details>

#### SimdF32x8 is permanently unavailable on ARM32

- SimdF32x8 is permanently unavailable on ARM32
- Verify: SimdF32x8 is permanently unavailable on ARM32
   - Expected: arm32_permanently_unavailable(TargetIdiom.SimdF32x8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SimdF32x8 is permanently unavailable on ARM32")
step("Verify: SimdF32x8 is permanently unavailable on ARM32")
expect(arm32_permanently_unavailable(TargetIdiom.SimdF32x8)).to_equal(true)
```

</details>

#### Crc32U64 is permanently unavailable on ARM32

- Crc32U64 is permanently unavailable on ARM32
- Verify: Crc32U64 is permanently unavailable on ARM32
   - Expected: arm32_permanently_unavailable(TargetIdiom.Crc32U64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Crc32U64 is permanently unavailable on ARM32")
step("Verify: Crc32U64 is permanently unavailable on ARM32")
expect(arm32_permanently_unavailable(TargetIdiom.Crc32U64)).to_equal(true)
```

</details>

#### ClmulLo is permanently unavailable on ARM32

- ClmulLo is permanently unavailable on ARM32
- Verify: ClmulLo is permanently unavailable on ARM32
   - Expected: arm32_permanently_unavailable(TargetIdiom.ClmulLo) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ClmulLo is permanently unavailable on ARM32")
step("Verify: ClmulLo is permanently unavailable on ARM32")
expect(arm32_permanently_unavailable(TargetIdiom.ClmulLo)).to_equal(true)
```

</details>

#### ClmulHi is permanently unavailable on ARM32

- ClmulHi is permanently unavailable on ARM32
- Verify: ClmulHi is permanently unavailable on ARM32
   - Expected: arm32_permanently_unavailable(TargetIdiom.ClmulHi) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ClmulHi is permanently unavailable on ARM32")
step("Verify: ClmulHi is permanently unavailable on ARM32")
expect(arm32_permanently_unavailable(TargetIdiom.ClmulHi)).to_equal(true)
```

</details>

#### RotateLeft is NOT permanently unavailable

- RotateLeft is NOT permanently unavailable
- Verify: RotateLeft is NOT permanently unavailable
   - Expected: arm32_permanently_unavailable(TargetIdiom.RotateLeft) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RotateLeft is NOT permanently unavailable")
step("Verify: RotateLeft is NOT permanently unavailable")
expect(arm32_permanently_unavailable(TargetIdiom.RotateLeft)).to_equal(false)
```

</details>

#### AesEnc is NOT permanently unavailable (optional extension exists)

- AesEnc is NOT permanently unavailable (optional extension exists)
- Verify: AesEnc is NOT permanently unavailable (optional extension exists)
   - Expected: arm32_permanently_unavailable(TargetIdiom.AesEnc) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc is NOT permanently unavailable (optional extension exists)")
step("Verify: AesEnc is NOT permanently unavailable (optional extension exists)")
expect(arm32_permanently_unavailable(TargetIdiom.AesEnc)).to_equal(false)
```

</details>

#### SimdI32x4 is NOT permanently unavailable (NEON provides it)

- SimdI32x4 is NOT permanently unavailable (NEON provides it)
- Verify: SimdI32x4 is NOT permanently unavailable (NEON provides it)
   - Expected: arm32_permanently_unavailable(TargetIdiom.SimdI32x4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SimdI32x4 is NOT permanently unavailable (NEON provides it)")
step("Verify: SimdI32x4 is NOT permanently unavailable (NEON provides it)")
expect(arm32_permanently_unavailable(TargetIdiom.SimdI32x4)).to_equal(false)
```

</details>

### ARM32 lowering — Cortex-M0 baseline decisions

#### RotateLeft is lowered natively on Cortex-M0

- RotateLeft is lowered natively on Cortex-M0
- Verify: RotateLeft is lowered natively on Cortex-M0
   - Expected: d.lowered is true
   - Expected: d.fallback is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RotateLeft is lowered natively on Cortex-M0")
step("Verify: RotateLeft is lowered natively on Cortex-M0")
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.RotateLeft)
expect(d.lowered).to_equal(true)
expect(d.fallback).to_equal(false)
```

</details>

#### ByteSwap is lowered natively on Cortex-M0 (REV instruction)

- ByteSwap is lowered natively on Cortex-M0 (REV instruction)
- Verify: ByteSwap is lowered natively on Cortex-M0 (REV instruction)
   - Expected: d.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ByteSwap is lowered natively on Cortex-M0 (REV instruction)")
step("Verify: ByteSwap is lowered natively on Cortex-M0 (REV instruction)")
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.ByteSwap)
expect(d.lowered).to_equal(true)
```

</details>

#### AesEnc falls back on Cortex-M0 (no AES extension)

- AesEnc falls back on Cortex-M0 (no AES extension)
- Verify: AesEnc falls back on Cortex-M0 (no AES extension)
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc falls back on Cortex-M0 (no AES extension)")
step("Verify: AesEnc falls back on Cortex-M0 (no AES extension)")
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.AesEnc)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
expect(d.reason.len()).to_be_greater_than(0)
```

</details>

#### SimdI32x4 falls back on Cortex-M0 (no NEON)

- SimdI32x4 falls back on Cortex-M0 (no NEON)
- Verify: SimdI32x4 falls back on Cortex-M0 (no NEON)
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SimdI32x4 falls back on Cortex-M0 (no NEON)")
step("Verify: SimdI32x4 falls back on Cortex-M0 (no NEON)")
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.SimdI32x4)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### Sha512Rounds2 falls back with permanent unavailability reason

- Sha512Rounds2 falls back with permanent unavailability reason
- Verify: Sha512Rounds2 falls back with permanent unavailability reason
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha512Rounds2 falls back with permanent unavailability reason")
step("Verify: Sha512Rounds2 falls back with permanent unavailability reason")
val caps = arm_caps_from_target("thumbv6m-none-eabi")
val d = arm32_lowering_decision(caps, TargetIdiom.Sha512Rounds2)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

### ARM32 lowering — neon+crypto triple decisions

#### AesEnc is lowered natively with AES extension

- AesEnc is lowered natively with AES extension
- Verify: AesEnc is lowered natively with AES extension
   - Expected: d.lowered is true
   - Expected: d.fallback is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc is lowered natively with AES extension")
step("Verify: AesEnc is lowered natively with AES extension")
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.AesEnc)
expect(d.lowered).to_equal(true)
expect(d.fallback).to_equal(false)
```

</details>

#### Sha256Rounds2 is lowered natively with SHA2 extension

- Sha256Rounds2 is lowered natively with SHA2 extension
- Verify: Sha256Rounds2 is lowered natively with SHA2 extension
   - Expected: d.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha256Rounds2 is lowered natively with SHA2 extension")
step("Verify: Sha256Rounds2 is lowered natively with SHA2 extension")
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.Sha256Rounds2)
expect(d.lowered).to_equal(true)
```

</details>

#### SimdI32x4 is lowered natively with NEON

- SimdI32x4 is lowered natively with NEON
- Verify: SimdI32x4 is lowered natively with NEON
   - Expected: d.lowered is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SimdI32x4 is lowered natively with NEON")
step("Verify: SimdI32x4 is lowered natively with NEON")
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.SimdI32x4)
expect(d.lowered).to_equal(true)
```

</details>

#### Sha512Rounds2 still falls back even with full crypto (permanent limit)

- Sha512Rounds2 still falls back even with full crypto (permanent limit)
- Verify: Sha512Rounds2 still falls back even with full crypto (permanent limit)
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sha512Rounds2 still falls back even with full crypto (permanent limit)")
step("Verify: Sha512Rounds2 still falls back even with full crypto (permanent limit)")
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.Sha512Rounds2)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### SimdI32x8 still falls back (no 256-bit NEON on ARM32)

- SimdI32x8 still falls back (no 256-bit NEON on ARM32)
- Verify: SimdI32x8 still falls back (no 256-bit NEON on ARM32)
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SimdI32x8 still falls back (no 256-bit NEON on ARM32)")
step("Verify: SimdI32x8 still falls back (no 256-bit NEON on ARM32)")
val caps = arm_caps_from_target("armv8-neon-crypto")
val d = arm32_lowering_decision(caps, TargetIdiom.SimdI32x8)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

### ARM32 lowering — scalar narrow-form helpers

#### CLZ is always available

- CLZ is always available
- Verify: CLZ is always available
   - Expected: arm32_clz_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CLZ is always available")
step("Verify: CLZ is always available")
expect(arm32_clz_available()).to_equal(true)
```

</details>

#### RBIT is always available (ARMv6T2+)

- RBIT is always available (ARMv6T2+)
- Verify: RBIT is always available (ARMv6T2+)
   - Expected: arm32_rbit_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RBIT is always available (ARMv6T2+)")
step("Verify: RBIT is always available (ARMv6T2+)")
expect(arm32_rbit_available()).to_equal(true)
```

</details>

#### REV is always available (ARMv6+)

- REV is always available (ARMv6+)
- Verify: REV is always available (ARMv6+)
   - Expected: arm32_rev_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REV is always available (ARMv6+)")
step("Verify: REV is always available (ARMv6+)")
expect(arm32_rev_available()).to_equal(true)
```

</details>

#### ROL 1 via ROR is 31 (32 - 1)

- ROL 1 via ROR is 31 (32 - 1)
- Verify: ROL 1 via ROR is 31 (32 - 1)
   - Expected: arm32_rotate_left_via_ror(1) equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROL 1 via ROR is 31 (32 - 1)")
step("Verify: ROL 1 via ROR is 31 (32 - 1)")
expect(arm32_rotate_left_via_ror(1)).to_equal(31)
```

</details>

#### ROL 8 via ROR is 24 (32 - 8)

- ROL 8 via ROR is 24 (32 - 8)
- Verify: ROL 8 via ROR is 24 (32 - 8)
   - Expected: arm32_rotate_left_via_ror(8) equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROL 8 via ROR is 24 (32 - 8)")
step("Verify: ROL 8 via ROR is 24 (32 - 8)")
expect(arm32_rotate_left_via_ror(8)).to_equal(24)
```

</details>

#### ROL 32 via ROR is 0 (identity)

- ROL 32 via ROR is 0 (identity)
- Verify: ROL 32 via ROR is 0 (identity)
   - Expected: arm32_rotate_left_via_ror(32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ROL 32 via ROR is 0 (identity)")
step("Verify: ROL 32 via ROR is 0 (identity)")
expect(arm32_rotate_left_via_ror(32)).to_equal(0)
```

</details>

### RV32 lowering — scalar narrow-form hooks

#### rv32 without Zbb has no native popcount

- rv32 without Zbb has no native popcount
- Verify: rv32 without Zbb has no native popcount
   - Expected: rv32_popcount_native(caps) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 without Zbb has no native popcount")
step("Verify: rv32 without Zbb has no native popcount")
val caps = rv32_caps_from_target("riscv32imac")
expect(rv32_popcount_native(caps)).to_equal(false)
```

</details>

#### rv32 with Zbb has native popcount

- rv32 with Zbb has native popcount
- Verify: rv32 with Zbb has native popcount
   - Expected: rv32_popcount_native(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zbb has native popcount")
step("Verify: rv32 with Zbb has native popcount")
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_popcount_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb has native CLZ

- rv32 with Zbb has native CLZ
- Verify: rv32 with Zbb has native CLZ
   - Expected: rv32_clz_native(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zbb has native CLZ")
step("Verify: rv32 with Zbb has native CLZ")
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_clz_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb has native CTZ

- rv32 with Zbb has native CTZ
- Verify: rv32 with Zbb has native CTZ
   - Expected: rv32_ctz_native(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zbb has native CTZ")
step("Verify: rv32 with Zbb has native CTZ")
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_ctz_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb has native byte-swap

- rv32 with Zbb has native byte-swap
- Verify: rv32 with Zbb has native byte-swap
   - Expected: rv32_bswap_native(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zbb has native byte-swap")
step("Verify: rv32 with Zbb has native byte-swap")
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_bswap_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb but not Zbkb does not have native bit-reverse

- rv32 with Zbb but not Zbkb does not have native bit-reverse
- Verify: rv32 with Zbb but not Zbkb does not have native bit-reverse
   - Expected: rv32_bitrev_native(caps) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zbb but not Zbkb does not have native bit-reverse")
step("Verify: rv32 with Zbb but not Zbkb does not have native bit-reverse")
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_bitrev_native(caps)).to_equal(false)
```

</details>

#### rv32 with Zbb+Zbkb has native bit-reverse

- rv32 with Zbb+Zbkb has native bit-reverse
- Verify: rv32 with Zbb+Zbkb has native bit-reverse
   - Expected: rv32_bitrev_native(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zbb+Zbkb has native bit-reverse")
step("Verify: rv32 with Zbb+Zbkb has native bit-reverse")
val caps = rv32_caps_from_target("riscv32imac_zbb_zbkb")
expect(rv32_bitrev_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zbb has native rotate

- rv32 with Zbb has native rotate
- Verify: rv32 with Zbb has native rotate
   - Expected: rv32_rotate_native(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zbb has native rotate")
step("Verify: rv32 with Zbb has native rotate")
val caps = rv32_caps_from_target("riscv32imac_zbb")
expect(rv32_rotate_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zkne has native AES encrypt

- rv32 with Zkne has native AES encrypt
- Verify: rv32 with Zkne has native AES encrypt
   - Expected: rv32_aes_enc_native(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zkne has native AES encrypt")
step("Verify: rv32 with Zkne has native AES encrypt")
val caps = rv32_caps_from_target("riscv32imac_zkne")
expect(rv32_aes_enc_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zknd has native AES decrypt

- rv32 with Zknd has native AES decrypt
- Verify: rv32 with Zknd has native AES decrypt
   - Expected: rv32_aes_dec_native(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zknd has native AES decrypt")
step("Verify: rv32 with Zknd has native AES decrypt")
val caps = rv32_caps_from_target("riscv32imac_zknd")
expect(rv32_aes_dec_native(caps)).to_equal(true)
```

</details>

#### rv32 with Zknh has native SHA-256

- rv32 with Zknh has native SHA-256
- Verify: rv32 with Zknh has native SHA-256
   - Expected: rv32_sha256_native(caps) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 with Zknh has native SHA-256")
step("Verify: rv32 with Zknh has native SHA-256")
val caps = rv32_caps_from_target("riscv32imac_zknh")
expect(rv32_sha256_native(caps)).to_equal(true)
```

</details>

#### rv32 baseline has no native AES

- rv32 baseline has no native AES
- Verify: rv32 baseline has no native AES
   - Expected: rv32_aes_enc_native(caps) is false
   - Expected: rv32_aes_dec_native(caps) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rv32 baseline has no native AES")
step("Verify: rv32 baseline has no native AES")
val caps = rv32_caps_from_target("riscv32imac")
expect(rv32_aes_enc_native(caps)).to_equal(false)
expect(rv32_aes_dec_native(caps)).to_equal(false)
```

</details>

### RV32 lowering — decision predicates

#### SHA-512 is always a fallback on RV32

- SHA-512 is always a fallback on RV32
- Verify: SHA-512 is always a fallback on RV32
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-512 is always a fallback on RV32")
step("Verify: SHA-512 is always a fallback on RV32")
val caps = rv32_caps_from_target("riscv32imac_zknd_zkne_zknh")
val d = rv32_lowering_decision(caps, TargetIdiom.Sha512Rounds2)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
expect(d.reason.len()).to_be_greater_than(0)
```

</details>

#### CRC32 is always a fallback on RV32 (no hardware CRC in RISC-V)

- CRC32 is always a fallback on RV32 (no hardware CRC in RISC-V)
- Verify: CRC32 is always a fallback on RV32 (no hardware CRC in RISC-V)
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CRC32 is always a fallback on RV32 (no hardware CRC in RISC-V)")
step("Verify: CRC32 is always a fallback on RV32 (no hardware CRC in RISC-V)")
val caps = rv32_caps_from_target("riscv32imac")
val d = rv32_lowering_decision(caps, TargetIdiom.Crc32U32)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### ClmulLo is a fallback on RV32 (Zbc not guaranteed)

- ClmulLo is a fallback on RV32 (Zbc not guaranteed)
- Verify: ClmulLo is a fallback on RV32 (Zbc not guaranteed)
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ClmulLo is a fallback on RV32 (Zbc not guaranteed)")
step("Verify: ClmulLo is a fallback on RV32 (Zbc not guaranteed)")
val caps = rv32_caps_from_target("riscv32imac")
val d = rv32_lowering_decision(caps, TargetIdiom.ClmulLo)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### SimdI32x8 is always a fallback on RV32

- SimdI32x8 is always a fallback on RV32
- Verify: SimdI32x8 is always a fallback on RV32
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SimdI32x8 is always a fallback on RV32")
step("Verify: SimdI32x8 is always a fallback on RV32")
val caps = rv32_caps_from_target("riscv32imac_zbb")
val d = rv32_lowering_decision(caps, TargetIdiom.SimdI32x8)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
```

</details>

#### RotateLeft is natively lowered with Zbb

- RotateLeft is natively lowered with Zbb
- Verify: RotateLeft is natively lowered with Zbb
   - Expected: d.lowered is true
   - Expected: d.fallback is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("RotateLeft is natively lowered with Zbb")
step("Verify: RotateLeft is natively lowered with Zbb")
val caps = rv32_caps_from_target("riscv32imac_zbb")
val d = rv32_lowering_decision(caps, TargetIdiom.RotateLeft)
expect(d.lowered).to_equal(true)
expect(d.fallback).to_equal(false)
```

</details>

#### AesEnc is natively lowered with Zkne

- AesEnc is natively lowered with Zkne
- Verify: AesEnc is natively lowered with Zkne
   - Expected: d.lowered is true
   - Expected: d.fallback is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc is natively lowered with Zkne")
step("Verify: AesEnc is natively lowered with Zkne")
val caps = rv32_caps_from_target("riscv32imac_zkne")
val d = rv32_lowering_decision(caps, TargetIdiom.AesEnc)
expect(d.lowered).to_equal(true)
expect(d.fallback).to_equal(false)
```

</details>

#### AesEnc falls back without Zkne

- AesEnc falls back without Zkne
- Verify: AesEnc falls back without Zkne
   - Expected: d.lowered is false
   - Expected: d.fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AesEnc falls back without Zkne")
step("Verify: AesEnc falls back without Zkne")
val caps = rv32_caps_from_target("riscv32imac")
val d = rv32_lowering_decision(caps, TargetIdiom.AesEnc)
expect(d.lowered).to_equal(false)
expect(d.fallback).to_equal(true)
expect(d.reason.len()).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-ARM32-LOWERING-PERMANENTLY-UNAVAILABLE-I-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd2f9052a38e96fc7d9cc371b048570474e7580a08cc90fd2d78fd4a25189df6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd2f9052a38e96fc7d9cc371b048570474e7580a08cc90fd2d78fd4a25189df6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd2f9052a38e96fc7d9cc371b048570474e7580a08cc90fd2d78fd4a25189df6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/intrinsic_lowering_arm32_spec.spl
mirror: doc/06_spec/unit/compiler/backend/intrinsic_lowering_arm32_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/intrinsic_lowering_arm32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/intrinsic_lowering_arm32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/intrinsic_lowering_arm32_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/intrinsic_lowering_arm32_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Sha512Rounds2 is permanently unavailable on ARM32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/intrinsic_lowering_arm32_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Sha512Msg1 is permanently unavailable on ARM32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/intrinsic_lowering_arm32_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Sha512Msg2 is permanently unavailable on ARM32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
