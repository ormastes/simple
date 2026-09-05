# avx512_emit_spec

> Purpose: Prove that AVX-512 EVEX emit VADDPS f32 golden.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# avx512_emit_spec

Purpose: Prove that AVX-512 EVEX emit VADDPS f32 golden.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/avx512_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that AVX-512 EVEX emit VADDPS f32 golden.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### AVX-512 EVEX emit VADDPS f32 golden

#### VADDPS zmm0 zmm0 zmm0 emits 6 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- VADDPS zmm0 zmm0 zmm0 emits 6 bytes
- Verify: VADDPS zmm0 zmm0 zmm0 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VADDPS zmm0 zmm0 zmm0 emits 6 bytes")
step("Verify: VADDPS zmm0 zmm0 zmm0 emits 6 bytes")
# @req: REQ-COMP-AVX-512-EVEX-EMIT-VADDPS-F32-GOLDEN-001
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result.len()).to_equal(6)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 escape byte is 0x62

- VADDPS zmm0 zmm0 zmm0 escape byte is 0x62
- Verify: VADDPS zmm0 zmm0 zmm0 escape byte is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VADDPS zmm0 zmm0 zmm0 escape byte is 0x62")
step("Verify: VADDPS zmm0 zmm0 zmm0 escape byte is 0x62")
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[0]).to_equal(98)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 P0 is 0xF1

- VADDPS zmm0 zmm0 zmm0 P0 is 0xF1
- Verify: VADDPS zmm0 zmm0 zmm0 P0 is 0xF1
   - Expected: result[1] equals `241`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VADDPS zmm0 zmm0 zmm0 P0 is 0xF1")
step("Verify: VADDPS zmm0 zmm0 zmm0 P0 is 0xF1")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 m2=0 m1=0 m0=1 = 0xF1 (mm=001=0F map)
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[1]).to_equal(241)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 P1 is 0x7C

- VADDPS zmm0 zmm0 zmm0 P1 is 0x7C
- Verify: VADDPS zmm0 zmm0 zmm0 P1 is 0x7C
   - Expected: result[2] equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VADDPS zmm0 zmm0 zmm0 P1 is 0x7C")
step("Verify: VADDPS zmm0 zmm0 zmm0 P1 is 0x7C")
# P1: W=0 ~vvvv=1111 must-1 pp=00 = 0x7C
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[2]).to_equal(124)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 P2 is 0x48

- VADDPS zmm0 zmm0 zmm0 P2 is 0x48
- Verify: VADDPS zmm0 zmm0 zmm0 P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VADDPS zmm0 zmm0 zmm0 P2 is 0x48")
step("Verify: VADDPS zmm0 zmm0 zmm0 P2 is 0x48")
# P2: z=0 L'=1 L=0 b=0 ~V'=1 aaa=000 = 0x48
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[3]).to_equal(72)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 opcode is 0x58

- VADDPS zmm0 zmm0 zmm0 opcode is 0x58
- Verify: VADDPS zmm0 zmm0 zmm0 opcode is 0x58
   - Expected: result[4] equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VADDPS zmm0 zmm0 zmm0 opcode is 0x58")
step("Verify: VADDPS zmm0 zmm0 zmm0 opcode is 0x58")
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[4]).to_equal(88)
```

</details>

#### VADDPS zmm0 zmm0 zmm0 ModRM is 0xC0

- VADDPS zmm0 zmm0 zmm0 ModRM is 0xC0
- Verify: VADDPS zmm0 zmm0 zmm0 ModRM is 0xC0
   - Expected: result[5] equals `192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VADDPS zmm0 zmm0 zmm0 ModRM is 0xC0")
step("Verify: VADDPS zmm0 zmm0 zmm0 ModRM is 0xC0")
val result = encode_avx512_add_f32x16(48, 48, 48, 80, false)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 EVEX emit VMULPS f32 golden

#### VMULPS zmm0 zmm0 zmm0 emits 6 bytes

- VMULPS zmm0 zmm0 zmm0 emits 6 bytes
- Verify: VMULPS zmm0 zmm0 zmm0 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMULPS zmm0 zmm0 zmm0 emits 6 bytes")
step("Verify: VMULPS zmm0 zmm0 zmm0 emits 6 bytes")
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result.len()).to_equal(6)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 escape byte is 0x62

- VMULPS zmm0 zmm0 zmm0 escape byte is 0x62
- Verify: VMULPS zmm0 zmm0 zmm0 escape byte is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMULPS zmm0 zmm0 zmm0 escape byte is 0x62")
step("Verify: VMULPS zmm0 zmm0 zmm0 escape byte is 0x62")
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[0]).to_equal(98)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 P0 is 0xF1

- VMULPS zmm0 zmm0 zmm0 P0 is 0xF1
- Verify: VMULPS zmm0 zmm0 zmm0 P0 is 0xF1
   - Expected: result[1] equals `241`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMULPS zmm0 zmm0 zmm0 P0 is 0xF1")
step("Verify: VMULPS zmm0 zmm0 zmm0 P0 is 0xF1")
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[1]).to_equal(241)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 P1 is 0x7C

- VMULPS zmm0 zmm0 zmm0 P1 is 0x7C
- Verify: VMULPS zmm0 zmm0 zmm0 P1 is 0x7C
   - Expected: result[2] equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMULPS zmm0 zmm0 zmm0 P1 is 0x7C")
step("Verify: VMULPS zmm0 zmm0 zmm0 P1 is 0x7C")
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[2]).to_equal(124)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 P2 is 0x48

- VMULPS zmm0 zmm0 zmm0 P2 is 0x48
- Verify: VMULPS zmm0 zmm0 zmm0 P2 is 0x48
   - Expected: result[3] equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMULPS zmm0 zmm0 zmm0 P2 is 0x48")
step("Verify: VMULPS zmm0 zmm0 zmm0 P2 is 0x48")
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[3]).to_equal(72)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 opcode is 0x59

- VMULPS zmm0 zmm0 zmm0 opcode is 0x59
- Verify: VMULPS zmm0 zmm0 zmm0 opcode is 0x59
   - Expected: result[4] equals `89`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMULPS zmm0 zmm0 zmm0 opcode is 0x59")
step("Verify: VMULPS zmm0 zmm0 zmm0 opcode is 0x59")
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[4]).to_equal(89)
```

</details>

#### VMULPS zmm0 zmm0 zmm0 ModRM is 0xC0

- VMULPS zmm0 zmm0 zmm0 ModRM is 0xC0
- Verify: VMULPS zmm0 zmm0 zmm0 ModRM is 0xC0
   - Expected: result[5] equals `192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VMULPS zmm0 zmm0 zmm0 ModRM is 0xC0")
step("Verify: VMULPS zmm0 zmm0 zmm0 ModRM is 0xC0")
val result = encode_avx512_mul_f32x16(48, 48, 48, 80, false)
expect(result[5]).to_equal(192)
```

</details>

### AVX-512 EVEX emit VFMADD213PS f32 golden

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 emits 6 bytes

- VFMADD213PS zmm0-k1-z zmm1 zmm2 emits 6 bytes
- Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 emits 6 bytes
   - Expected: result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VFMADD213PS zmm0-k1-z zmm1 zmm2 emits 6 bytes")
step("Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 emits 6 bytes")
# ZMM0=48, ZMM1=49, ZMM2=50, K1=81
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result.len()).to_equal(6)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 escape byte is 0x62

- VFMADD213PS zmm0-k1-z zmm1 zmm2 escape byte is 0x62
- Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 escape byte is 0x62
   - Expected: result[0] equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VFMADD213PS zmm0-k1-z zmm1 zmm2 escape byte is 0x62")
step("Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 escape byte is 0x62")
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[0]).to_equal(98)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 P0 is 0xF2

- VFMADD213PS zmm0-k1-z zmm1 zmm2 P0 is 0xF2
- Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 P0 is 0xF2
   - Expected: result[1] equals `242`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VFMADD213PS zmm0-k1-z zmm1 zmm2 P0 is 0xF2")
step("Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 P0 is 0xF2")
# P0: ~R=1 ~X=1 ~B=1 ~R'=1 0 m2=0 m1=1 m0=0 = 0xF2 (MAP2=0F38)
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[1]).to_equal(242)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 P1 is 0x75

- VFMADD213PS zmm0-k1-z zmm1 zmm2 P1 is 0x75
- Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 P1 is 0x75
   - Expected: result[2] equals `117`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VFMADD213PS zmm0-k1-z zmm1 zmm2 P1 is 0x75")
step("Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 P1 is 0x75")
# P1: W=0 ~vvvv=1110(zmm1) must-1 pp=01(0x66) = 0x75
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[2]).to_equal(117)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 P2 is 0xC9

- VFMADD213PS zmm0-k1-z zmm1 zmm2 P2 is 0xC9
- Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 P2 is 0xC9
   - Expected: result[3] equals `201`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VFMADD213PS zmm0-k1-z zmm1 zmm2 P2 is 0xC9")
step("Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 P2 is 0xC9")
# P2: z=1 L'=1 L=0 b=0 ~V'=1 aaa=001 = 0xC9
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[3]).to_equal(201)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 opcode is 0xA8

- VFMADD213PS zmm0-k1-z zmm1 zmm2 opcode is 0xA8
- Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 opcode is 0xA8
   - Expected: result[4] equals `168`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VFMADD213PS zmm0-k1-z zmm1 zmm2 opcode is 0xA8")
step("Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 opcode is 0xA8")
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[4]).to_equal(168)
```

</details>

#### VFMADD213PS zmm0-k1-z zmm1 zmm2 ModRM is 0xC2

- VFMADD213PS zmm0-k1-z zmm1 zmm2 ModRM is 0xC2
- Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 ModRM is 0xC2
   - Expected: result[5] equals `194`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VFMADD213PS zmm0-k1-z zmm1 zmm2 ModRM is 0xC2")
step("Verify: VFMADD213PS zmm0-k1-z zmm1 zmm2 ModRM is 0xC2")
# ModRM: mod=11 reg=0(zmm0) rm=2(zmm2) = 0xC2
val result = encode_avx512_fma_f32x16(48, 49, 50, 81, true)
expect(result[5]).to_equal(194)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-AVX-512-EVEX-EMIT-VADDPS-F32-GOLDEN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d0b9872d639d91976d172eaf5cc74a7925b131d18fa072336179d3f61277c30d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d0b9872d639d91976d172eaf5cc74a7925b131d18fa072336179d3f61277c30d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d0b9872d639d91976d172eaf5cc74a7925b131d18fa072336179d3f61277c30d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/avx512_emit_spec.spl
mirror: doc/06_spec/unit/compiler/backend/avx512_emit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/avx512_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/avx512_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/avx512_emit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/avx512_emit_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VADDPS zmm0 zmm0 zmm0 emits 6 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_emit_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VADDPS zmm0 zmm0 zmm0 escape byte is 0x62' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/avx512_emit_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'VADDPS zmm0 zmm0 zmm0 P0 is 0xF1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
