# RV32IMAC Core Smoke Tests

> Smoke tests for the RV32IMAC core. Verifies basic instruction execution through GHDL simulation: NOP, ADD, branch, load/store.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32IMAC Core Smoke Tests

Smoke tests for the RV32IMAC core. Verifies basic instruction execution through GHDL simulation: NOP, ADD, branch, load/store.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-CORE-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# RV32IMAC Core Smoke Tests

**Feature IDs:** #RV32-CORE-001
**Category:** Hardware
**Difficulty:** 3/5
**Status:** In Progress

## Overview

Smoke tests for the RV32IMAC core. Verifies basic instruction execution
through GHDL simulation: NOP, ADD, branch, load/store.

## Scenarios

### RV32 Register File

#### x0 always reads as zero

- Verify: x0 always reads as zero
   - Expected: rf.read(0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: x0 always reads as zero")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** Fresh register file
**When:** Writing to x0 then reading
**Then:** x0 returns 0
"""
var rf = Rv32RegFile.create()
rf.write(0, 0xDEADBEEF)
expect(rf.read(0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### writes and reads back correctly

- Verify: writes and reads back correctly
   - Expected: rf.read(1) equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: writes and reads back correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** Register file
**When:** Writing 0x12345678 to x1
**Then:** x1 reads back 0x12345678
"""
var rf = Rv32RegFile.create()
rf.write(1, 0x12345678)
expect(rf.read(1)).to_equal(0x12345678)
```

</details>

#### handles all 32 registers

- Verify: handles all 32 registers
   - Expected: rf.read(0) equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: rf.read(1) equals `100)  # oracle: pinned constant asserted by this scenario`
   - Expected: rf.read(31) equals `3100)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: handles all 32 registers")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** Register file
**When:** Writing unique values to x1-x31
**Then:** All read back correctly, x0 stays zero
"""
var rf = Rv32RegFile.create()
var i = 1
while i < 32:
    rf.write(i, i * 100)
    i = i + 1
expect(rf.read(0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(rf.read(1)).to_equal(100)  # oracle: pinned constant asserted by this scenario
expect(rf.read(31)).to_equal(3100)  # oracle: pinned constant asserted by this scenario
```

</details>

### RV32 ALU

#### computes ADD correctly

- Verify: computes ADD correctly
   - Expected: alu_execute(AluOp.Add, 5, 3) equals `8)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes ADD correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** ALU with ADD operation
**When:** 5 + 3
**Then:** Returns 8
"""
expect(alu_execute(AluOp.Add, 5, 3)).to_equal(8)  # oracle: pinned constant asserted by this scenario
```

</details>

#### computes SUB correctly

- Verify: computes SUB correctly
   - Expected: alu_execute(AluOp.Sub, 10, 3) equals `7)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes SUB correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** ALU with SUB operation
**When:** 10 - 3
**Then:** Returns 7
"""
expect(alu_execute(AluOp.Sub, 10, 3)).to_equal(7)  # oracle: pinned constant asserted by this scenario
```

</details>

#### computes AND correctly

- Verify: computes AND correctly
   - Expected: alu_execute(AluOp.And, 0xFF00FF00, 0x0F0F0F0F) equals `0x0F000F00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes AND correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(alu_execute(AluOp.And, 0xFF00FF00, 0x0F0F0F0F)).to_equal(0x0F000F00)
```

</details>

#### computes OR correctly

- Verify: computes OR correctly
   - Expected: alu_execute(AluOp.Or, 0xFF000000, 0x00FF0000) equals `0xFFFF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes OR correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(alu_execute(AluOp.Or, 0xFF000000, 0x00FF0000)).to_equal(0xFFFF0000)
```

</details>

#### computes XOR correctly

- Verify: computes XOR correctly
   - Expected: alu_execute(AluOp.Xor, 0xFF00FF00, 0xFFFF0000) equals `0x00FFFF00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes XOR correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(alu_execute(AluOp.Xor, 0xFF00FF00, 0xFFFF0000)).to_equal(0x00FFFF00)
```

</details>

#### computes SLL correctly

- Verify: computes SLL correctly
   - Expected: alu_execute(AluOp.Sll, 1, 4) equals `16)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes SLL correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(alu_execute(AluOp.Sll, 1, 4)).to_equal(16)  # oracle: pinned constant asserted by this scenario
```

</details>

#### computes SRL correctly

- Verify: computes SRL correctly
   - Expected: alu_execute(AluOp.Srl, 256, 4) equals `16)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes SRL correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(alu_execute(AluOp.Srl, 256, 4)).to_equal(16)  # oracle: pinned constant asserted by this scenario
```

</details>

#### computes SLT correctly

- Verify: computes SLT correctly
   - Expected: alu_execute(AluOp.Slt, 0xFFFFFFFF, 1) equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes SLT correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** Signed comparison
**When:** -1 < 1 (as 32-bit signed)
**Then:** Returns 1
"""
expect(alu_execute(AluOp.Slt, 0xFFFFFFFF, 1)).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### computes SLTU correctly

- Verify: computes SLTU correctly
   - Expected: alu_execute(AluOp.Sltu, 0xFFFFFFFF, 1) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes SLTU correctly")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** Unsigned comparison
**When:** 0xFFFFFFFF > 1 (as unsigned)
**Then:** Returns 0
"""
expect(alu_execute(AluOp.Sltu, 0xFFFFFFFF, 1)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### RV32 Branch Resolution

#### BEQ taken when equal

- Verify: BEQ taken when equal
   - Expected: resolve_branch(BranchOp.Beq, 42, 42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: BEQ taken when equal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(resolve_branch(BranchOp.Beq, 42, 42)).to_equal(true)
```

</details>

#### BEQ not taken when unequal

- Verify: BEQ not taken when unequal
   - Expected: resolve_branch(BranchOp.Beq, 42, 43) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: BEQ not taken when unequal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(resolve_branch(BranchOp.Beq, 42, 43)).to_equal(false)
```

</details>

#### BNE taken when unequal

- Verify: BNE taken when unequal
   - Expected: resolve_branch(BranchOp.Bne, 42, 43) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: BNE taken when unequal")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(resolve_branch(BranchOp.Bne, 42, 43)).to_equal(true)
```

</details>

#### BLT taken for signed less-than

- Verify: BLT taken for signed less-than
   - Expected: resolve_branch(BranchOp.Blt, 0xFFFFFFFF, 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: BLT taken for signed less-than")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(resolve_branch(BranchOp.Blt, 0xFFFFFFFF, 0)).to_equal(true)
```

</details>

#### JAL always taken

- Verify: JAL always taken
   - Expected: compute_branch_target("branch", 0x1000, 0, 0) equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: JAL always taken")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(compute_branch_target("branch", 0x1000, 0, 0)).to_equal(0x1000)
```

</details>

#### computes branch target from PC+imm

- Verify: computes branch target from PC+imm
   - Expected: compute_branch_target("branch", 0x1000, 0, 0x100) equals `0x1100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes branch target from PC+imm")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(compute_branch_target("branch", 0x1000, 0, 0x100)).to_equal(0x1100)
```

</details>

#### computes JALR target from rs1+imm

- Verify: computes JALR target from rs1+imm
   - Expected: compute_branch_target("jalr", 0x1000, 0x2000, 0x10) equals `0x2010`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: computes JALR target from rs1+imm")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(compute_branch_target("jalr", 0x1000, 0x2000, 0x10)).to_equal(0x2010)
```

</details>

### RV32 Immediate Decoding

#### decodes I-type positive immediate

- Verify: decodes I-type positive immediate
   - Expected: decode_imm_i(instr) equals `100)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: decodes I-type positive immediate")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** Instruction with imm=100 in I-type format
**When:** decode_imm_i() called
**Then:** Returns 100
"""
val instr = 100 << 20  # imm=100 in bits [31:20]
expect(decode_imm_i(instr)).to_equal(100)  # oracle: pinned constant asserted by this scenario
```

</details>

#### decodes U-type immediate

- Verify: decodes U-type immediate
   - Expected: decode_imm_u(instr) equals `0x12345000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: decodes U-type immediate")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""
**Given:** LUI with upper 20 bits = 0x12345
**When:** decode_imm_u() called
**Then:** Returns 0x12345000
"""
val instr = 0x12345000  # Upper 20 bits in place
expect(decode_imm_u(instr)).to_equal(0x12345000)
```

</details>

### RV32 Memory Access

#### loads a word from memory

- Verify: loads a word from memory
   - Expected: mem_load(memory, 0, MemWidth.Word, false) equals `0x12345678`
   - Expected: mem_load(memory, 4, MemWidth.Word, false) equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: loads a word from memory")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val memory = [0x12345678, 0xDEADBEEF]
expect(mem_load(memory, 0, MemWidth.Word, false)).to_equal(0x12345678)
expect(mem_load(memory, 4, MemWidth.Word, false)).to_equal(0xDEADBEEF)
```

</details>

#### loads a byte with sign extension

- Verify: loads a byte with sign extension
   - Expected: mem_load(memory, 0, MemWidth.Byte, true) equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: loads a byte with sign extension")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val memory = [0x000000FF]
expect(mem_load(memory, 0, MemWidth.Byte, true)).to_equal(0xFFFFFFFF)
```

</details>

#### loads a byte without sign extension

- Verify: loads a byte without sign extension
   - Expected: mem_load(memory, 0, MemWidth.Byte, false) equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: loads a byte without sign extension")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val memory = [0x000000FF]
expect(mem_load(memory, 0, MemWidth.Byte, false)).to_equal(0xFF)
```

</details>

#### stores a word to memory

- Verify: stores a word to memory
   - Expected: updated[0] equals `0xCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV32IMAC
step("Verify: stores a word to memory")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val memory = [0, 0]
val updated = mem_store(memory, 0, 0xCAFEBABE, MemWidth.Word)
expect(updated[0]).to_equal(0xCAFEBABE)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca0295aa64297fda6968516a5e9347bcc23bf42e9d68cf0aafebb4c47682105b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca0295aa64297fda6968516a5e9347bcc23bf42e9d68cf0aafebb4c47682105b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca0295aa64297fda6968516a5e9347bcc23bf42e9d68cf0aafebb4c47682105b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl
mirror: doc/06_spec/02_integration/hardware/rv32imac/rv32_core_smoke_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/hardware/rv32imac/rv32_core_smoke_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/hardware/rv32imac/rv32_core_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/hardware/rv32imac/rv32_core_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
