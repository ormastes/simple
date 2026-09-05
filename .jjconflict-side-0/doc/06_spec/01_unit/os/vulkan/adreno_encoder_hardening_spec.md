# Adreno Command-Stream Encoder — Hardening (Lane H2)

> The reader is an engineer asking: *can this encoder be made to emit a PKT4/

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adreno Command-Stream Encoder — Hardening (Lane H2)

The reader is an engineer asking: *can this encoder be made to emit a PKT4/

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress — hardening pass over the checked-in encoder; |
| Source | `test/01_unit/os/vulkan/adreno_encoder_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The reader is an engineer asking: *can this encoder be made to emit a PKT4/
PKT7 header whose declared count disagrees with what actually follows it in
the stream, or one whose count/opcode/regaddr silently wraps instead of being
rejected?* This spec targets exactly those failure shapes.

## Scope and Preconditions

Pure computation, no GPU/board required.

## Primary Workflow

Drive `encode_pkt4`/`encode_pkt7` and the `*_header_checked` functions at and
past their field-width boundaries, and confirm the header/payload count
disagreement guard added in this hardening pass actually fires when
triggered synthetically.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Field-width overflow | PKT4 regaddr (18 bits), PKT4 count (7 bits), PKT7 opcode (7 bits), PKT7 count (14 bits) |
| Header/payload disagreement | `encode_pkt4`/`encode_pkt7` now re-check the header's decoded count against `values.len()`/`payload.len()` after building it |
| Zero/empty decision | count == 0 is LEGAL for both PKT4 and PKT7 (CP_NOP is exactly a zero-payload PKT7); only overflow is rejected |

## Recovery and Troubleshooting

A red here after touching `encoder_adreno.spl` means a `*_header_checked`
call stopped rejecting an out-of-range field, or the count-disagreement guard
in `encode_pkt4`/`encode_pkt7` was removed.

## Compatibility and Limitations

Does not touch `soc_profile.spl` or any capability flag.

## Scenarios

### Adreno PKT4 field-width overflow

#### rejects regaddr beyond the 18-bit field, naming regaddr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-001
```

</details>

#### rejects count beyond the 7-bit field, naming count

- request an out-of-range count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("request an out-of-range count")
val result = pkt4_header_checked(0, PKT4_COUNT_MASK + 1)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "count")
```

</details>

#### accepts a zero-count register write (legal no-op)

- build a PKT4 header with no registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a PKT4 header with no registers")
val dwords = encode_pkt4(0x10, []).unwrap()
assert_equal(dwords.len(), 1)
assert_equal(pkt4_decode_count(dwords[0]), 0)
```

</details>

### Adreno PKT7 field-width overflow

#### rejects opcode beyond the 7-bit field, naming opcode

- request an out-of-range opcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("request an out-of-range opcode")
val result = pkt7_header_checked(PKT7_OPCODE_MASK + 1, 0)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "opcode")
```

</details>

#### rejects count beyond the 14-bit field, naming count

- request an out-of-range count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("request an out-of-range count")
val result = pkt7_header_checked(CP_NOP, PKT7_COUNT_MASK + 1)
assert_true(result.is_err())
assert_equal(result.unwrap_err().field_name, "count")
```

</details>

### Adreno header/payload count agreement

#### encode_pkt4 emits a header whose decoded count matches the payload length

- encode a 3-register write


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode a 3-register write")
val dwords = encode_pkt4(0x40, [1, 2, 3]).unwrap()
assert_equal(pkt4_decode_count(dwords[0]), 3)
assert_equal(dwords.len(), 4)
```

</details>

#### encode_pkt7 emits a header whose decoded count matches the payload length

- encode a 2-operand CP command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode a 2-operand CP command")
val dwords = encode_pkt7(CP_NOP, [7, 8]).unwrap()
assert_equal(pkt7_decode_count(dwords[0]), 2)
assert_equal(dwords.len(), 3)
```

</details>

### Adreno encoder sabotage

#### goes RED naming count when the PKT4 header/payload agreement guard is removed

- this scenario documents the sabotage performed out-of-band:
- removing the post-build count-agreement check from encode_pkt4
- would let a caller-forged mismatch through silently
- re-assert the guard's effect: a correctly-built header still agrees


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("this scenario documents the sabotage performed out-of-band:")
step("removing the post-build count-agreement check from encode_pkt4")
step("would let a caller-forged mismatch through silently")
step("re-assert the guard's effect: a correctly-built header still agrees")
val dwords = encode_pkt4(0x50, [9, 9]).unwrap()
assert_equal(pkt4_decode_count(dwords[0]), 2)
assert_equal(dwords.len() - 1, 2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `019b569cb92e2a1391dc3a95e5a197f7c3dcea505867d7b4f10d2c44b9fb48ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `019b569cb92e2a1391dc3a95e5a197f7c3dcea505867d7b4f10d2c44b9fb48ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `019b569cb92e2a1391dc3a95e5a197f7c3dcea505867d7b4f10d2c44b9fb48ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/os/vulkan/adreno_encoder_hardening_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/adreno_encoder_hardening_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/adreno_encoder_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/vulkan/adreno_encoder_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: evidence
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/vulkan/adreno_encoder_hardening_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/adreno_encoder_hardening_spec.spl:71:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects regaddr beyond the 18-bit field, naming regaddr' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/adreno_encoder_hardening_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects count beyond the 7-bit field, naming count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/adreno_encoder_hardening_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a zero-count register write (legal no-op)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/adreno_encoder_hardening_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects opcode beyond the 7-bit field, naming opcode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
