# neon_crc32_spec

> Purpose: Prove that emit_neon_crc32b — CRC-32 byte accumulate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# neon_crc32_spec

Purpose: Prove that emit_neon_crc32b — CRC-32 byte accumulate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/neon_crc32_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that emit_neon_crc32b — CRC-32 byte accumulate.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### emit_neon_crc32b — CRC-32 byte accumulate

#### CRC32B W0, W0, W0 encodes to base opcode bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- CRC32B W0, W0, W0 encodes to base opcode bytes
- Verify: CRC32B W0, W0, W0 encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x40`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32B W0, W0, W0 encodes to base opcode bytes")
step("Verify: CRC32B W0, W0, W0 encodes to base opcode bytes")
# @req: REQ-COMP-EMIT-NEON-CRC32B-CRC-32-BYTE-ACCUMULATE-001
var b = emit_neon_crc32b(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

#### CRC32B W1, W2, W3 encodes register fields correctly

- CRC32B W1, W2, W3 encodes register fields correctly
- Verify: CRC32B W1, W2, W3 encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x41`
   - Expected: b[1] equals `0x40`
   - Expected: b[2] equals `0xC3`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32B W1, W2, W3 encodes register fields correctly")
step("Verify: CRC32B W1, W2, W3 encodes register fields correctly")
# word = 0x1AC04000 + 3*65536 + 2*32 + 1 = 0x1AC34041
# LE bytes: 0x41, 0x40, 0xC3, 0x1A
var b = emit_neon_crc32b(1, 2, 3)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x41)
expect(b[1]).to_equal(0x40)
expect(b[2]).to_equal(0xC3)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32h — CRC-32 halfword accumulate

#### CRC32H W0, W0, W0 encodes to base opcode bytes

- CRC32H W0, W0, W0 encodes to base opcode bytes
- Verify: CRC32H W0, W0, W0 encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x44`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32H W0, W0, W0 encodes to base opcode bytes")
step("Verify: CRC32H W0, W0, W0 encodes to base opcode bytes")
var b = emit_neon_crc32h(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x44)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32w — CRC-32 word accumulate

#### CRC32W W0, W0, W0 encodes to base opcode bytes

- CRC32W W0, W0, W0 encodes to base opcode bytes
- Verify: CRC32W W0, W0, W0 encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32W W0, W0, W0 encodes to base opcode bytes")
step("Verify: CRC32W W0, W0, W0 encodes to base opcode bytes")
var b = emit_neon_crc32w(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

#### CRC32W W0, W0, W1 encodes Rm=1 correctly

- CRC32W W0, W0, W1 encodes Rm=1 correctly
- Verify: CRC32W W0, W0, W1 encodes Rm=1 correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x48`
   - Expected: b[2] equals `0xC1`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32W W0, W0, W1 encodes Rm=1 correctly")
step("Verify: CRC32W W0, W0, W1 encodes Rm=1 correctly")
var b = emit_neon_crc32w(0, 0, 1)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x48)
expect(b[2]).to_equal(0xC1)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32x — CRC-32 doubleword accumulate

#### CRC32X W0, W0, X0 encodes to base opcode bytes

- CRC32X W0, W0, X0 encodes to base opcode bytes
- Verify: CRC32X W0, W0, X0 encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x4C`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x9A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32X W0, W0, X0 encodes to base opcode bytes")
step("Verify: CRC32X W0, W0, X0 encodes to base opcode bytes")
var b = emit_neon_crc32x(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x4C)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x9A)
```

</details>

### emit_neon_crc32cb — CRC-32C byte accumulate

#### CRC32CB W0, W0, W0 encodes to base opcode bytes

- CRC32CB W0, W0, W0 encodes to base opcode bytes
- Verify: CRC32CB W0, W0, W0 encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x50`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32CB W0, W0, W0 encodes to base opcode bytes")
step("Verify: CRC32CB W0, W0, W0 encodes to base opcode bytes")
var b = emit_neon_crc32cb(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x50)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32ch — CRC-32C halfword accumulate

#### CRC32CH W0, W0, W0 encodes to base opcode bytes

- CRC32CH W0, W0, W0 encodes to base opcode bytes
- Verify: CRC32CH W0, W0, W0 encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x54`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32CH W0, W0, W0 encodes to base opcode bytes")
step("Verify: CRC32CH W0, W0, W0 encodes to base opcode bytes")
var b = emit_neon_crc32ch(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x54)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32cw — CRC-32C word accumulate

#### CRC32CW W0, W0, W0 encodes to base opcode bytes

- CRC32CW W0, W0, W0 encodes to base opcode bytes
- Verify: CRC32CW W0, W0, W0 encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x58`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x1A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32CW W0, W0, W0 encodes to base opcode bytes")
step("Verify: CRC32CW W0, W0, W0 encodes to base opcode bytes")
var b = emit_neon_crc32cw(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x58)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x1A)
```

</details>

### emit_neon_crc32cx — CRC-32C doubleword accumulate

#### CRC32CX W0, W0, X0 encodes to base opcode bytes

- CRC32CX W0, W0, X0 encodes to base opcode bytes
- Verify: CRC32CX W0, W0, X0 encodes to base opcode bytes
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0x00`
   - Expected: b[1] equals `0x5C`
   - Expected: b[2] equals `0xC0`
   - Expected: b[3] equals `0x9A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32CX W0, W0, X0 encodes to base opcode bytes")
step("Verify: CRC32CX W0, W0, X0 encodes to base opcode bytes")
var b = emit_neon_crc32cx(0, 0, 0)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0x00)
expect(b[1]).to_equal(0x5C)
expect(b[2]).to_equal(0xC0)
expect(b[3]).to_equal(0x9A)
```

</details>

#### CRC32CX W5, W6, X7 encodes register fields correctly

- CRC32CX W5, W6, X7 encodes register fields correctly
- Verify: CRC32CX W5, W6, X7 encodes register fields correctly
   - Expected: b.len() equals `4`
   - Expected: b[0] equals `0xC5`
   - Expected: b[1] equals `0x5C`
   - Expected: b[2] equals `0xC7`
   - Expected: b[3] equals `0x9A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC32CX W5, W6, X7 encodes register fields correctly")
step("Verify: CRC32CX W5, W6, X7 encodes register fields correctly")
# word = 0x9AC05C00 + 7*65536 + 6*32 + 5 = 0x9AC75CC5
# LE bytes: 0xC5, 0x5C, 0xC7, 0x9A
var b = emit_neon_crc32cx(5, 6, 7)
expect(b.len()).to_equal(4)
expect(b[0]).to_equal(0xC5)
expect(b[1]).to_equal(0x5C)
expect(b[2]).to_equal(0xC7)
expect(b[3]).to_equal(0x9A)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-EMIT-NEON-CRC32B-CRC-32-BYTE-ACCUMULATE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1a8858c951489f52e28d2bc4e4e66d2569701be0eba3d0134c82b4a8ab0401cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a8858c951489f52e28d2bc4e4e66d2569701be0eba3d0134c82b4a8ab0401cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a8858c951489f52e28d2bc4e4e66d2569701be0eba3d0134c82b4a8ab0401cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/backend/neon_crc32_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/neon_crc32_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/neon_crc32_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/neon_crc32_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/neon_crc32_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/neon_crc32_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CRC32B W0, W0, W0 encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_crc32_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CRC32B W1, W2, W3 encodes register fields correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/neon_crc32_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CRC32H W0, W0, W0 encodes to base opcode bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
