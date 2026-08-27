# neon_dot_spec

> Purpose: Prove that emit_neon_sdot_4s — signed int8 dot product 4 lanes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_dot_spec

Purpose: Prove that emit_neon_sdot_4s — signed int8 dot product 4 lanes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_dot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that emit_neon_sdot_4s — signed int8 dot product 4 lanes.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### emit_neon_sdot_4s — signed int8 dot product 4 lanes

#### SDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes
- Verify: SDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x80`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes")
step("Verify: SDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes")
# @req: REQ-COMP-EMIT-NEON-SDOT-4S-SIGNED-INT8-DOT-PRODUC-001
var b = emit_neon_sdot_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x4E)
```

</details>

#### SDOT V1.4S, V2.16B, V3.16B encodes register fields correctly

- SDOT V1.4S, V2.16B, V3.16B encodes register fields correctly
- Verify: SDOT V1.4S, V2.16B, V3.16B encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x83`
   - Expected: b[3] equals `0x4E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SDOT V1.4S, V2.16B, V3.16B encodes register fields correctly")
step("Verify: SDOT V1.4S, V2.16B, V3.16B encodes register fields correctly")
# word = 0x4E809400 + 3*65536 + 2*32 + 1 = 0x4E839441
# LE bytes: 0x41, 0x94, 0x83, 0x4E
var b = emit_neon_sdot_4s(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x83)
expect(b[3]).to_equal(0x4E)
```

</details>

### emit_neon_udot_4s — unsigned int8 dot product 4 lanes

#### UDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes

- UDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes
- Verify: UDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x80`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("UDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes")
step("Verify: UDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes")
var b = emit_neon_udot_4s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x6E)
```

</details>

#### UDOT V5.4S, V6.16B, V7.16B encodes register fields correctly

- UDOT V5.4S, V6.16B, V7.16B encodes register fields correctly
- Verify: UDOT V5.4S, V6.16B, V7.16B encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0xC5`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x87`
   - Expected: b[3] equals `0x6E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("UDOT V5.4S, V6.16B, V7.16B encodes register fields correctly")
step("Verify: UDOT V5.4S, V6.16B, V7.16B encodes register fields correctly")
# word = 0x6E809400 + 7*65536 + 6*32 + 5 = 0x6E8794C5
# LE bytes: 0xC5, 0x94, 0x87, 0x6E
var b = emit_neon_udot_4s(5, 6, 7)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0xC5)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x87)
expect(b[3]).to_equal(0x6E)
```

</details>

### emit_neon_sdot_2s — signed int8 dot product 2 lanes

#### SDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes

- SDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes
- Verify: SDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x80`
   - Expected: b[3] equals `0x0E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("SDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes")
step("Verify: SDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes")
var b = emit_neon_sdot_2s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x0E)
```

</details>

### emit_neon_udot_2s — unsigned int8 dot product 2 lanes

#### UDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes

- UDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes
- Verify: UDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x94`
   - Expected: b[2] equals `0x80`
   - Expected: b[3] equals `0x2E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("UDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes")
step("Verify: UDOT V0.2S, V0.8B, V0.8B encodes to base opcode bytes")
var b = emit_neon_udot_2s(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x94)
expect(b[2]).to_equal(0x80)
expect(b[3]).to_equal(0x2E)
```

</details>

### SDOT/UDOT emit output length

#### emit_neon_sdot_4s always returns 4 bytes

- emit_neon_sdot_4s always returns 4 bytes
- Verify: emit_neon_sdot_4s always returns 4 bytes
   - Expected: b.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emit_neon_sdot_4s always returns 4 bytes")
step("Verify: emit_neon_sdot_4s always returns 4 bytes")
var b = emit_neon_sdot_4s(1, 2, 3)
expect(b.len()).to_equal(4)
```

</details>

### SDOT vs UDOT byte[3] distinction

#### SDOT and UDOT 4S with same registers match bytes 0-2 and differ at byte[3]

- SDOT and UDOT 4S with same registers match bytes 0-2 and differ at byte[3]
- Verify: SDOT and UDOT 4S with same registers match bytes 0-2 and differ at byte[3]
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
step("SDOT and UDOT 4S with same registers match bytes 0-2 and differ at byte[3]")
step("Verify: SDOT and UDOT 4S with same registers match bytes 0-2 and differ at byte[3]")
var s = emit_neon_sdot_4s(1, 2, 3)
var u = emit_neon_udot_4s(1, 2, 3)
expect(s[0]).to_equal(u[0])
expect(s[1]).to_equal(u[1])
expect(s[2]).to_equal(u[2])
# UDOT has U=1 (bit 29), which raises byte[3] by 0x20
expect(u[3] - s[3]).to_equal(0x20)
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

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-EMIT-NEON-SDOT-4S-SIGNED-INT8-DOT-PRODUC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58aa586578beddff7e9b2cd60984813f8dd093688261cf72d1f6d5c97be75da4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58aa586578beddff7e9b2cd60984813f8dd093688261cf72d1f6d5c97be75da4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58aa586578beddff7e9b2cd60984813f8dd093688261cf72d1f6d5c97be75da4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/neon_dot_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/neon_dot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/neon_dot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/neon_dot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/neon_dot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/neon_dot_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_dot_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SDOT V1.4S, V2.16B, V3.16B encodes register fields correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_dot_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UDOT V0.4S, V0.16B, V0.16B encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
