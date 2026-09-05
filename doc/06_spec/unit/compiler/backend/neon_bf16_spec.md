# neon_bf16_spec

> Purpose: Prove that emit_bfdot_v4bf16 — BF16 dot product 64-bit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_bf16_spec

Purpose: Prove that emit_bfdot_v4bf16 — BF16 dot product 64-bit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/neon_bf16_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that emit_bfdot_v4bf16 — BF16 dot product 64-bit.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### emit_bfdot_v4bf16 — BF16 dot product 64-bit

#### BFDOT V0.2S, V0.4H, V0.4H encodes to base opcode bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- BFDOT V0.2S, V0.4H, V0.4H encodes to base opcode bytes
- Verify: BFDOT V0.2S, V0.4H, V0.4H encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xFC`
   - Expected: b[2] equals `0x40`
   - Expected: b[3] equals `0x2E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BFDOT V0.2S, V0.4H, V0.4H encodes to base opcode bytes")
step("Verify: BFDOT V0.2S, V0.4H, V0.4H encodes to base opcode bytes")
# @req: REQ-COMP-EMIT-BFDOT-V4BF16-BF16-DOT-PRODUCT-64-BI-001
var b = emit_bfdot_v4bf16(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xFC)
expect(b[2]).to_equal(0x40)
expect(b[3]).to_equal(0x2E)
```

</details>

#### BFDOT V1.2S, V2.4H, V3.4H encodes register fields correctly

- BFDOT V1.2S, V2.4H, V3.4H encodes register fields correctly
- Verify: BFDOT V1.2S, V2.4H, V3.4H encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xFC`
   - Expected: b[2] equals `0x43`
   - Expected: b[3] equals `0x2E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BFDOT V1.2S, V2.4H, V3.4H encodes register fields correctly")
step("Verify: BFDOT V1.2S, V2.4H, V3.4H encodes register fields correctly")
# word = 0x2E40FC00 + 3*65536 + 2*32 + 1 = 0x2E43FC41
# LE bytes: 0x41, 0xFC, 0x43, 0x2E
var b = emit_bfdot_v4bf16(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0xFC)
expect(b[2]).to_equal(0x43)
expect(b[3]).to_equal(0x2E)
```

</details>

#### emit_bfdot_v4bf16 always returns 4 bytes

- emit_bfdot_v4bf16 always returns 4 bytes
- Verify: emit_bfdot_v4bf16 always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_bfdot_v4bf16 always returns 4 bytes")
step("Verify: emit_bfdot_v4bf16 always returns 4 bytes")
var b = emit_bfdot_v4bf16(5, 6, 7)
expect(b.len()).to_equal(4)
```

</details>

### emit_bfmmla_v4bf16 — BF16 matrix multiply-accumulate 128-bit

#### BFMMLA V0.4S, V0.8H, V0.8H encodes to base opcode bytes

- BFMMLA V0.4S, V0.8H, V0.8H encodes to base opcode bytes
- Verify: BFMMLA V0.4S, V0.8H, V0.8H encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0xEC`
   - Expected: b[2] equals `0x40`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BFMMLA V0.4S, V0.8H, V0.8H encodes to base opcode bytes")
step("Verify: BFMMLA V0.4S, V0.8H, V0.8H encodes to base opcode bytes")
var b = emit_bfmmla_v4bf16(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0xEC)
expect(b[2]).to_equal(0x40)
expect(b[3]).to_equal(0x6E)
```

</details>

#### BFMMLA V1.4S, V2.8H, V3.8H encodes register fields correctly

- BFMMLA V1.4S, V2.8H, V3.8H encodes register fields correctly
- Verify: BFMMLA V1.4S, V2.8H, V3.8H encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0xEC`
   - Expected: b[2] equals `0x43`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BFMMLA V1.4S, V2.8H, V3.8H encodes register fields correctly")
step("Verify: BFMMLA V1.4S, V2.8H, V3.8H encodes register fields correctly")
# word = 0x6E40EC00 + 3*65536 + 2*32 + 1 = 0x6E43EC41
# LE bytes: 0x41, 0xEC, 0x43, 0x6E
var b = emit_bfmmla_v4bf16(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0xEC)
expect(b[2]).to_equal(0x43)
expect(b[3]).to_equal(0x6E)
```

</details>

#### emit_bfmmla_v4bf16 always returns 4 bytes

- emit_bfmmla_v4bf16 always returns 4 bytes
- Verify: emit_bfmmla_v4bf16 always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_bfmmla_v4bf16 always returns 4 bytes")
step("Verify: emit_bfmmla_v4bf16 always returns 4 bytes")
var b = emit_bfmmla_v4bf16(5, 6, 7)
expect(b.len()).to_equal(4)
```

</details>

### emit_bfcvtn_v4bf16 — narrow float32 to bfloat16 lower half

#### BFCVTN V0.4H, V0.4S encodes to base opcode bytes

- BFCVTN V0.4H, V0.4S encodes to base opcode bytes
- Verify: BFCVTN V0.4H, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BFCVTN V0.4H, V0.4S encodes to base opcode bytes")
step("Verify: BFCVTN V0.4H, V0.4S encodes to base opcode bytes")
var b = emit_bfcvtn_v4bf16(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x0E)
```

</details>

#### BFCVTN V1.4H, V2.4S encodes register fields correctly

- BFCVTN V1.4H, V2.4S encodes register fields correctly
- Verify: BFCVTN V1.4H, V2.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BFCVTN V1.4H, V2.4S encodes register fields correctly")
step("Verify: BFCVTN V1.4H, V2.4S encodes register fields correctly")
# word = 0x0EA16800 + 2*32 + 1 = 0x0EA16841
# LE bytes: 0x41, 0x68, 0xA1, 0x0E
var b = emit_bfcvtn_v4bf16(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x0E)
```

</details>

#### emit_bfcvtn_v4bf16 always returns 4 bytes

- emit_bfcvtn_v4bf16 always returns 4 bytes
- Verify: emit_bfcvtn_v4bf16 always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_bfcvtn_v4bf16 always returns 4 bytes")
step("Verify: emit_bfcvtn_v4bf16 always returns 4 bytes")
var b = emit_bfcvtn_v4bf16(3, 4)
expect(b.len()).to_equal(4)
```

</details>

### emit_bfcvtn2_v8bf16 — narrow float32 to bfloat16 upper half

#### BFCVTN2 V0.8H, V0.4S encodes to base opcode bytes

- BFCVTN2 V0.8H, V0.4S encodes to base opcode bytes
- Verify: BFCVTN2 V0.8H, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BFCVTN2 V0.8H, V0.4S encodes to base opcode bytes")
step("Verify: BFCVTN2 V0.8H, V0.4S encodes to base opcode bytes")
var b = emit_bfcvtn2_v8bf16(0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x4E)
```

</details>

#### BFCVTN2 V1.8H, V2.4S encodes register fields correctly

- BFCVTN2 V1.8H, V2.4S encodes register fields correctly
- Verify: BFCVTN2 V1.8H, V2.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x68`
   - Expected: b[2] equals `0xA1`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BFCVTN2 V1.8H, V2.4S encodes register fields correctly")
step("Verify: BFCVTN2 V1.8H, V2.4S encodes register fields correctly")
# word = 0x4EA16800 + 2*32 + 1 = 0x4EA16841
# LE bytes: 0x41, 0x68, 0xA1, 0x4E
var b = emit_bfcvtn2_v8bf16(1, 2)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x68)
expect(b[2]).to_equal(0xA1)
expect(b[3]).to_equal(0x4E)
```

</details>

#### emit_bfcvtn2_v8bf16 always returns 4 bytes

- emit_bfcvtn2_v8bf16 always returns 4 bytes
- Verify: emit_bfcvtn2_v8bf16 always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit_bfcvtn2_v8bf16 always returns 4 bytes")
step("Verify: emit_bfcvtn2_v8bf16 always returns 4 bytes")
var b = emit_bfcvtn2_v8bf16(3, 4)
expect(b.len()).to_equal(4)
```

</details>

### BFCVTN vs BFCVTN2 Q-bit distinction

#### BFCVTN and BFCVTN2 with same regs match bytes 0-2 and differ at byte[3]

- BFCVTN and BFCVTN2 with same regs match bytes 0-2 and differ at byte[3]
- Verify: BFCVTN and BFCVTN2 with same regs match bytes 0-2 and differ at byte[3]
   - Expected: n[0] equals `n2[0]`
   - Expected: n[1] equals `n2[1]`
   - Expected: n[2] equals `n2[2]`
   - Expected: n2[3] - n[3] equals `0x40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BFCVTN and BFCVTN2 with same regs match bytes 0-2 and differ at byte[3]")
step("Verify: BFCVTN and BFCVTN2 with same regs match bytes 0-2 and differ at byte[3]")
var n = emit_bfcvtn_v4bf16(1, 2)
var n2 = emit_bfcvtn2_v8bf16(1, 2)
expect(n[0]).to_equal(n2[0])
expect(n[1]).to_equal(n2[1])
expect(n[2]).to_equal(n2[2])
# BFCVTN2 has Q=1 (bit 30), which raises byte[3] by 0x40
expect(n2[3] - n[3]).to_equal(0x40)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-EMIT-BFDOT-V4BF16-BF16-DOT-PRODUCT-64-BI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eb63b8b3b2fccb78043a19c58c0198155cb2371ec0e1980c69f3d56b9e56e97e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb63b8b3b2fccb78043a19c58c0198155cb2371ec0e1980c69f3d56b9e56e97e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb63b8b3b2fccb78043a19c58c0198155cb2371ec0e1980c69f3d56b9e56e97e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/neon_bf16_spec.spl
mirror: doc/06_spec/unit/compiler/backend/neon_bf16_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/neon_bf16_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/neon_bf16_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/neon_bf16_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/neon_bf16_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BFDOT V0.2S, V0.4H, V0.4H encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/neon_bf16_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'BFDOT V1.2S, V2.4H, V3.4H encodes register fields correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/neon_bf16_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emit_bfdot_v4bf16 always returns 4 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
