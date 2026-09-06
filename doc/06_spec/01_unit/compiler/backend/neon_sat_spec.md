# neon_sat_spec

> Purpose: Prove that emit_neon_sqadd_4s — signed saturating add 4 lanes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_sat_spec

Purpose: Prove that emit_neon_sqadd_4s — signed saturating add 4 lanes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_sat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that emit_neon_sqadd_4s — signed saturating add 4 lanes.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### emit_neon_sqadd_4s — signed saturating add 4 lanes

#### SQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: SQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x0C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: SQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
# @req: REQ-COMP-EMIT-NEON-SQADD-4S-SIGNED-SATURATING-ADD-001
var b = emit_neon_sqadd_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### SQADD V1.4S, V2.4S, V3.4S encodes register fields correctly

- SQADD V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: SQADD V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x0C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SQADD V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: SQADD V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x4EA00C00 + 3*65536 + 2*32 + 1 = 0x4EA30C41
# LE bytes: 0x41, 0x0C, 0xA3, 0x4E
var b = emit_neon_sqadd_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_neon_uqadd_4s — unsigned saturating add 4 lanes

#### UQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- UQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: UQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x0C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("UQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: UQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_neon_uqadd_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### UQADD V5.4S, V6.4S, V7.4S encodes register fields correctly

- UQADD V5.4S, V6.4S, V7.4S encodes register fields correctly
- Verify: UQADD V5.4S, V6.4S, V7.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0xC5`
   - Expected: b[1] equals `0x0C`
   - Expected: b[2] equals `0xA7`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("UQADD V5.4S, V6.4S, V7.4S encodes register fields correctly")
step("Verify: UQADD V5.4S, V6.4S, V7.4S encodes register fields correctly")
# word = 0x6EA00C00 + 7*65536 + 6*32 + 5 = 0x6EA70CC5
# LE bytes: 0xC5, 0x0C, 0xA7, 0x6E
var b = emit_neon_uqadd_4s(5, 6, 7)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0xC5)
expect(b[1]).to_equal(0x0C)
expect(b[2]).to_equal(0xA7)
expect(b[3]).to_equal(0x6E)
```

</details>

### emit_neon_sqsub_4s — signed saturating subtract 4 lanes

#### SQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- SQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: SQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x2C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: SQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_neon_sqsub_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x2C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x4E)
```

</details>

#### SQSUB V1.4S, V2.4S, V3.4S encodes register fields correctly

- SQSUB V1.4S, V2.4S, V3.4S encodes register fields correctly
- Verify: SQSUB V1.4S, V2.4S, V3.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x2C`
   - Expected: b[2] equals `0xA3`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SQSUB V1.4S, V2.4S, V3.4S encodes register fields correctly")
step("Verify: SQSUB V1.4S, V2.4S, V3.4S encodes register fields correctly")
# word = 0x4EA02C00 + 3*65536 + 2*32 + 1 = 0x4EA32C41
# LE bytes: 0x41, 0x2C, 0xA3, 0x4E
var b = emit_neon_sqsub_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x2C)
expect(b[2]).to_equal(0xA3)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_neon_uqsub_4s — unsigned saturating subtract 4 lanes

#### UQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes

- UQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes
- Verify: UQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x2C`
   - Expected: b[2] equals `0xA0`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("UQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
step("Verify: UQSUB V0.4S, V0.4S, V0.4S encodes to base opcode bytes")
var b = emit_neon_uqsub_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x2C)
expect(b[2]).to_equal(0xA0)
expect(b[3]).to_equal(0x6E)
```

</details>

#### UQSUB V5.4S, V6.4S, V7.4S encodes register fields correctly

- UQSUB V5.4S, V6.4S, V7.4S encodes register fields correctly
- Verify: UQSUB V5.4S, V6.4S, V7.4S encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0xC5`
   - Expected: b[1] equals `0x2C`
   - Expected: b[2] equals `0xA7`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("UQSUB V5.4S, V6.4S, V7.4S encodes register fields correctly")
step("Verify: UQSUB V5.4S, V6.4S, V7.4S encodes register fields correctly")
# word = 0x6EA02C00 + 7*65536 + 6*32 + 5 = 0x6EA72CC5
# LE bytes: 0xC5, 0x2C, 0xA7, 0x6E
var b = emit_neon_uqsub_4s(5, 6, 7)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0xC5)
expect(b[1]).to_equal(0x2C)
expect(b[2]).to_equal(0xA7)
expect(b[3]).to_equal(0x6E)
```

</details>

### SQADD/UQADD/SQSUB/UQSUB emit output length

#### emit_neon_sqadd_4s always returns 4 bytes

- emit_neon_sqadd_4s always returns 4 bytes
- Verify: emit_neon_sqadd_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_neon_sqadd_4s always returns 4 bytes")
step("Verify: emit_neon_sqadd_4s always returns 4 bytes")
var b = emit_neon_sqadd_4s(1, 2, 3)
expect(b.len()).to_equal(4)
```

</details>

#### emit_neon_uqsub_4s always returns 4 bytes

- emit_neon_uqsub_4s always returns 4 bytes
- Verify: emit_neon_uqsub_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_neon_uqsub_4s always returns 4 bytes")
step("Verify: emit_neon_uqsub_4s always returns 4 bytes")
var b = emit_neon_uqsub_4s(5, 6, 7)
expect(b.len()).to_equal(4)
```

</details>

### signed vs unsigned byte[3] distinction

#### SQADD and UQADD with same registers match bytes 0-2 and differ at byte[3]

- SQADD and UQADD with same registers match bytes 0-2 and differ at byte[3]
- Verify: SQADD and UQADD with same registers match bytes 0-2 and differ at byte[3]
   - Expected: s[0] equals `u[0]`
   - Expected: s[1] equals `u[1]`
   - Expected: s[2] equals `u[2]`
   - Expected: u[3] - s[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SQADD and UQADD with same registers match bytes 0-2 and differ at byte[3]")
step("Verify: SQADD and UQADD with same registers match bytes 0-2 and differ at byte[3]")
var s = emit_neon_sqadd_4s(1, 2, 3)
var u = emit_neon_uqadd_4s(1, 2, 3)
expect(s[0]).to_equal(u[0])
expect(s[1]).to_equal(u[1])
expect(s[2]).to_equal(u[2])
# UQADD has U=1 (bit 29), which raises byte[3] by 0x20
expect(u[3] - s[3]).to_equal(0x20)
```

</details>

#### SQSUB and UQSUB with same registers match bytes 0-2 and differ at byte[3]

- SQSUB and UQSUB with same registers match bytes 0-2 and differ at byte[3]
- Verify: SQSUB and UQSUB with same registers match bytes 0-2 and differ at byte[3]
   - Expected: s[0] equals `u[0]`
   - Expected: s[1] equals `u[1]`
   - Expected: s[2] equals `u[2]`
   - Expected: u[3] - s[3] equals `0x20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SQSUB and UQSUB with same registers match bytes 0-2 and differ at byte[3]")
step("Verify: SQSUB and UQSUB with same registers match bytes 0-2 and differ at byte[3]")
var s = emit_neon_sqsub_4s(1, 2, 3)
var u = emit_neon_uqsub_4s(1, 2, 3)
expect(s[0]).to_equal(u[0])
expect(s[1]).to_equal(u[1])
expect(s[2]).to_equal(u[2])
# UQSUB has U=1 (bit 29), which raises byte[3] by 0x20
expect(u[3] - s[3]).to_equal(0x20)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-EMIT-NEON-SQADD-4S-SIGNED-SATURATING-ADD-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ecaf44f6c259f52e7d8e8b67dc76e932c9fefccdb0fadb7d73e3ebba1f3bfa7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ecaf44f6c259f52e7d8e8b67dc76e932c9fefccdb0fadb7d73e3ebba1f3bfa7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ecaf44f6c259f52e7d8e8b67dc76e932c9fefccdb0fadb7d73e3ebba1f3bfa7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/neon_sat_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/neon_sat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/neon_sat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/neon_sat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/neon_sat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/neon_sat_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_sat_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SQADD V1.4S, V2.4S, V3.4S encodes register fields correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_sat_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UQADD V0.4S, V0.4S, V0.4S encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
