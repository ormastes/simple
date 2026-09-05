# RV64 Compressed Instructions Unit Tests

> Unit tests for RV64C compressed instruction detection and decompression. 16-bit instructions expand to 32-bit equivalents.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Compressed Instructions Unit Tests

Unit tests for RV64C compressed instruction detection and decompression. 16-bit instructions expand to 32-bit equivalents.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-COMPRESSED-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/unit/hardware/rv64gc/rv64_compressed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for RV64C compressed instruction detection and decompression.
16-bit instructions expand to 32-bit equivalents.

## Scenarios

### Compressed Detection

#### 16-bit instruction detected (bits 1:0 = 00)

- 16-bit instruction detected (bits 1:0 = 00)
   - Expected: is_compressed(0x4000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("16-bit instruction detected (bits 1:0 = 00)")
expect(is_compressed(0x4000)).to_equal(true)
```

</details>

#### 32-bit instruction not compressed (bits 1:0 = 11)

- 32-bit instruction not compressed (bits 1:0 = 11)
   - Expected: is_compressed(0x00A00513) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("32-bit instruction not compressed (bits 1:0 = 11)")
expect(is_compressed(0x00A00513)).to_equal(false)
```

</details>

### Register Mapping

#### rvc_reg(0) = 8

- rvc_reg(0) = 8
   - Expected: rvc_reg(0) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rvc_reg(0) = 8")
expect(rvc_reg(0)).to_equal(8)
```

</details>

#### rvc_reg(7) = 15

- rvc_reg(7) = 15
   - Expected: rvc_reg(7) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rvc_reg(7) = 15")
expect(rvc_reg(7)).to_equal(15)
```

</details>

### Quadrant 0 Decompression

#### C.ADDI4SPN: expands to ADDI rd', x2, nzuimm

- C.ADDI4SPN: expands to ADDI rd', x2, nzuimm
   - Expected: expanded and 0x7F equals `0x13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.ADDI4SPN: expands to ADDI rd', x2, nzuimm")
# C.ADDI4SPN x8, sp, 16 => ADDI x8, x2, 16
val compressed = 0x0040  # C.ADDI4SPN rd'=0(x8), nzuimm=16
val expanded = decompress_rvc(compressed)
# Verify opcode is OP_IMM (0x13)
expect(expanded and 0x7F).to_equal(0x13)
```

</details>

#### C.LW: expands to LW rd', offset(rs1')

- C.LW: expands to LW rd', offset(rs1')
   - Expected: expanded and 0x7F equals `0x03)  # LOAD opcode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.LW: expands to LW rd', offset(rs1')")
val compressed = 0x4188  # C.LW
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x03)  # LOAD opcode
```

</details>

#### C.LD: expands to LD rd', offset(rs1') (RV64 only)

- C.LD: expands to LD rd', offset(rs1') (RV64 only)
   - Expected: expanded and 0x7F equals `0x03)  # LOAD opcode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.LD: expands to LD rd', offset(rs1') (RV64 only)")
val compressed = 0x6188  # C.LD
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x03)  # LOAD opcode
```

</details>

#### C.SD: expands to SD rs2', offset(rs1') (RV64 only)

- C.SD: expands to SD rs2', offset(rs1') (RV64 only)
   - Expected: expanded and 0x7F equals `0x23)  # STORE opcode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.SD: expands to SD rs2', offset(rs1') (RV64 only)")
val compressed = 0xE188  # C.SD
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x23)  # STORE opcode
```

</details>

### Quadrant 1 Decompression

#### C.NOP: expands to ADDI x0, x0, 0

- C.NOP: expands to ADDI x0, x0, 0
   - Expected: expanded equals `0x00000013)  # ADDI x0, x0, 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.NOP: expands to ADDI x0, x0, 0")
val compressed = 0x0001  # C.NOP
val expanded = decompress_rvc(compressed)
expect(expanded).to_equal(0x00000013)  # ADDI x0, x0, 0
```

</details>

#### C.ADDI: expands to ADDI rd, rd, nzimm

- C.ADDI: expands to ADDI rd, rd, nzimm
   - Expected: expanded and 0x7F equals `0x13)  # OP_IMM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.ADDI: expands to ADDI rd, rd, nzimm")
val compressed = 0x0505  # C.ADDI x10, 1
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x13)  # OP_IMM
```

</details>

#### C.ADDIW: expands to ADDIW rd, rd, imm (RV64 only)

- C.ADDIW: expands to ADDIW rd, rd, imm (RV64 only)
   - Expected: expanded and 0x7F equals `0x1B)  # OP_IMM_32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.ADDIW: expands to ADDIW rd, rd, imm (RV64 only)")
val compressed = 0x2505  # C.ADDIW x10, 1
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x1B)  # OP_IMM_32
```

</details>

#### C.J: expands to JAL x0, offset

- C.J: expands to JAL x0, offset
   - Expected: expanded and 0x7F equals `0x6F)  # JAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.J: expands to JAL x0, offset")
val compressed = 0xA001  # C.J offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x6F)  # JAL
```

</details>

#### C.BEQZ: expands to BEQ rs1', x0, offset

- C.BEQZ: expands to BEQ rs1', x0, offset
   - Expected: expanded and 0x7F equals `0x63)  # BRANCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.BEQZ: expands to BEQ rs1', x0, offset")
val compressed = 0xC001  # C.BEQZ
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x63)  # BRANCH
```

</details>

#### C.BNEZ: expands to BNE rs1', x0, offset

- C.BNEZ: expands to BNE rs1', x0, offset
   - Expected: expanded and 0x7F equals `0x63)  # BRANCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.BNEZ: expands to BNE rs1', x0, offset")
val compressed = 0xE001  # C.BNEZ
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x63)  # BRANCH
```

</details>

### Quadrant 2 Decompression

#### C.SLLI: expands to SLLI rd, rd, shamt

- C.SLLI: expands to SLLI rd, rd, shamt
   - Expected: expanded and 0x7F equals `0x13)  # OP_IMM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.SLLI: expands to SLLI rd, rd, shamt")
val compressed = 0x0502  # C.SLLI x10, 1 (approx encoding)
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x13)  # OP_IMM
```

</details>

#### C.LDSP: expands to LD rd, offset(x2) (RV64 only)

- C.LDSP: expands to LD rd, offset(x2) (RV64 only)
   - Expected: expanded and 0x7F equals `0x03)  # LOAD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.LDSP: expands to LD rd, offset(x2) (RV64 only)")
val compressed = 0x6502  # C.LDSP x10, offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x03)  # LOAD
```

</details>

#### C.LWSP: expands to LW rd, offset(x2)

- C.LWSP: expands to LW rd, offset(x2)
   - Expected: expanded and 0x7F equals `0x03)  # LOAD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.LWSP: expands to LW rd, offset(x2)")
val compressed = 0x4502  # C.LWSP x10, offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x03)  # LOAD
```

</details>

#### C.SDSP: expands to SD rs2, offset(x2) (RV64 only)

- C.SDSP: expands to SD rs2, offset(x2) (RV64 only)
   - Expected: expanded and 0x7F equals `0x23)  # STORE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.SDSP: expands to SD rs2, offset(x2) (RV64 only)")
val compressed = 0xE50A  # C.SDSP x10, offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x23)  # STORE
```

</details>

#### C.SWSP: expands to SW rs2, offset(x2)

- C.SWSP: expands to SW rs2, offset(x2)
   - Expected: expanded and 0x7F equals `0x23)  # STORE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.SWSP: expands to SW rs2, offset(x2)")
val compressed = 0xC50A  # C.SWSP x10, offset
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x23)  # STORE
```

</details>

#### C.JR: expands to JALR x0, 0(rs1)

- C.JR: expands to JALR x0, 0(rs1)
   - Expected: expanded and 0x7F equals `0x67)  # JALR`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.JR: expands to JALR x0, 0(rs1)")
val compressed = 0x8502  # C.JR x10
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x67)  # JALR
```

</details>

#### C.MV: expands to ADD rd, x0, rs2

- C.MV: expands to ADD rd, x0, rs2
   - Expected: expanded and 0x7F equals `0x33)  # OP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.MV: expands to ADD rd, x0, rs2")
val compressed = 0x850A  # C.MV x10, x10 (approx)
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x33)  # OP
```

</details>

#### C.ADD: expands to ADD rd, rd, rs2

- C.ADD: expands to ADD rd, rd, rs2
   - Expected: expanded and 0x7F equals `0x33)  # OP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("C.ADD: expands to ADD rd, rd, rs2")
val compressed = 0x950A  # C.ADD x10, x10 (approx)
val expanded = decompress_rvc(compressed)
expect(expanded and 0x7F).to_equal(0x33)  # OP
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6f36b4d60524214b6c915e79161bf943a3c037271bfb776689f64a949b5fd6b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f36b4d60524214b6c915e79161bf943a3c037271bfb776689f64a949b5fd6b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f36b4d60524214b6c915e79161bf943a3c037271bfb776689f64a949b5fd6b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/hardware/rv64gc/rv64_compressed_spec.spl
mirror: doc/06_spec/unit/hardware/rv64gc/rv64_compressed_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/rv64gc/rv64_compressed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/rv64gc/rv64_compressed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/rv64gc/rv64_compressed_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/hardware/rv64gc/rv64_compressed_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '16-bit instruction detected (bits 1:0 = 00)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_compressed_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '32-bit instruction not compressed (bits 1:0 = 11)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/rv64gc/rv64_compressed_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rvc_reg(0) = 8' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
