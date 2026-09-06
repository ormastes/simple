# RV32IMAC Core Smoke Tests

> Smoke tests for the RV32IMAC core. Verifies basic instruction execution through GHDL simulation: NOP, ADD, branch, load/store.

<!-- sdn-diagram:id=rv32_core_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_core_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_core_smoke_spec -> std
rv32_core_smoke_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_core_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Smoke tests for the RV32IMAC core. Verifies basic instruction execution
through GHDL simulation: NOP, ADD, branch, load/store.

## Scenarios

### RV32 Register File

#### x0 always reads as zero

- x0 always reads as zero
   - Expected: rf.read(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x0 always reads as zero")
"""
**Given:** Fresh register file
**When:** Writing to x0 then reading
**Then:** x0 returns 0
"""
var rf = Rv32RegFile.create()
rf.write(0, 0xDEADBEEF)
expect(rf.read(0)).to_equal(0)
```

</details>

#### writes and reads back correctly

- writes and reads back correctly
   - Expected: rf.read(1) equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes and reads back correctly")
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

- handles all 32 registers
   - Expected: rf.read(0) equals `0`
   - Expected: rf.read(1) equals `100`
   - Expected: rf.read(31) equals `3100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles all 32 registers")
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
expect(rf.read(0)).to_equal(0)
expect(rf.read(1)).to_equal(100)
expect(rf.read(31)).to_equal(3100)
```

</details>

### RV32 ALU

#### computes ADD correctly

- computes ADD correctly
   - Expected: alu_execute(AluOp.Add, 5, 3) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes ADD correctly")
"""
**Given:** ALU with ADD operation
**When:** 5 + 3
**Then:** Returns 8
"""
expect(alu_execute(AluOp.Add, 5, 3)).to_equal(8)
```

</details>

#### computes SUB correctly

- computes SUB correctly
   - Expected: alu_execute(AluOp.Sub, 10, 3) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes SUB correctly")
"""
**Given:** ALU with SUB operation
**When:** 10 - 3
**Then:** Returns 7
"""
expect(alu_execute(AluOp.Sub, 10, 3)).to_equal(7)
```

</details>

#### computes AND correctly

- computes AND correctly
   - Expected: alu_execute(AluOp.And, 0xFF00FF00, 0x0F0F0F0F) equals `0x0F000F00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes AND correctly")
expect(alu_execute(AluOp.And, 0xFF00FF00, 0x0F0F0F0F)).to_equal(0x0F000F00)
```

</details>

#### computes OR correctly

- computes OR correctly
   - Expected: alu_execute(AluOp.Or, 0xFF000000, 0x00FF0000) equals `0xFFFF0000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes OR correctly")
expect(alu_execute(AluOp.Or, 0xFF000000, 0x00FF0000)).to_equal(0xFFFF0000)
```

</details>

#### computes XOR correctly

- computes XOR correctly
   - Expected: alu_execute(AluOp.Xor, 0xFF00FF00, 0xFFFF0000) equals `0x00FFFF00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes XOR correctly")
expect(alu_execute(AluOp.Xor, 0xFF00FF00, 0xFFFF0000)).to_equal(0x00FFFF00)
```

</details>

#### computes SLL correctly

- computes SLL correctly
   - Expected: alu_execute(AluOp.Sll, 1, 4) equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes SLL correctly")
expect(alu_execute(AluOp.Sll, 1, 4)).to_equal(16)
```

</details>

#### computes SRL correctly

- computes SRL correctly
   - Expected: alu_execute(AluOp.Srl, 256, 4) equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes SRL correctly")
expect(alu_execute(AluOp.Srl, 256, 4)).to_equal(16)
```

</details>

#### computes SLT correctly

- computes SLT correctly
   - Expected: alu_execute(AluOp.Slt, 0xFFFFFFFF, 1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes SLT correctly")
"""
**Given:** Signed comparison
**When:** -1 < 1 (as 32-bit signed)
**Then:** Returns 1
"""
expect(alu_execute(AluOp.Slt, 0xFFFFFFFF, 1)).to_equal(1)
```

</details>

#### computes SLTU correctly

- computes SLTU correctly
   - Expected: alu_execute(AluOp.Sltu, 0xFFFFFFFF, 1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes SLTU correctly")
"""
**Given:** Unsigned comparison
**When:** 0xFFFFFFFF > 1 (as unsigned)
**Then:** Returns 0
"""
expect(alu_execute(AluOp.Sltu, 0xFFFFFFFF, 1)).to_equal(0)
```

</details>

### RV32 Branch Resolution

#### BEQ taken when equal

- BEQ taken when equal
   - Expected: resolve_branch(BranchOp.Beq, 42, 42) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("BEQ taken when equal")
expect(resolve_branch(BranchOp.Beq, 42, 42)).to_equal(true)
```

</details>

#### BEQ not taken when unequal

- BEQ not taken when unequal
   - Expected: resolve_branch(BranchOp.Beq, 42, 43) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("BEQ not taken when unequal")
expect(resolve_branch(BranchOp.Beq, 42, 43)).to_equal(false)
```

</details>

#### BNE taken when unequal

- BNE taken when unequal
   - Expected: resolve_branch(BranchOp.Bne, 42, 43) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("BNE taken when unequal")
expect(resolve_branch(BranchOp.Bne, 42, 43)).to_equal(true)
```

</details>

#### BLT taken for signed less-than

- BLT taken for signed less-than
   - Expected: resolve_branch(BranchOp.Blt, 0xFFFFFFFF, 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("BLT taken for signed less-than")
expect(resolve_branch(BranchOp.Blt, 0xFFFFFFFF, 0)).to_equal(true)
```

</details>

#### JAL always taken

- JAL always taken
   - Expected: compute_branch_target("branch", 0x1000, 0, 0) equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("JAL always taken")
expect(compute_branch_target("branch", 0x1000, 0, 0)).to_equal(0x1000)
```

</details>

#### computes branch target from PC+imm

- computes branch target from PC+imm
   - Expected: compute_branch_target("branch", 0x1000, 0, 0x100) equals `0x1100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes branch target from PC+imm")
expect(compute_branch_target("branch", 0x1000, 0, 0x100)).to_equal(0x1100)
```

</details>

#### computes JALR target from rs1+imm

- computes JALR target from rs1+imm
   - Expected: compute_branch_target("jalr", 0x1000, 0x2000, 0x10) equals `0x2010`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("computes JALR target from rs1+imm")
expect(compute_branch_target("jalr", 0x1000, 0x2000, 0x10)).to_equal(0x2010)
```

</details>

### RV32 Immediate Decoding

#### decodes I-type positive immediate

- decodes I-type positive immediate
   - Expected: decode_imm_i(instr) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("decodes I-type positive immediate")
"""
**Given:** Instruction with imm=100 in I-type format
**When:** decode_imm_i() called
**Then:** Returns 100
"""
val instr = 100 << 20  # imm=100 in bits [31:20]
expect(decode_imm_i(instr)).to_equal(100)
```

</details>

#### decodes U-type immediate

- decodes U-type immediate
   - Expected: decode_imm_u(instr) equals `0x12345000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("decodes U-type immediate")
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

- loads a word from memory
   - Expected: mem_load(memory, 0, MemWidth.Word, false) equals `0x12345678`
   - Expected: mem_load(memory, 4, MemWidth.Word, false) equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("loads a word from memory")
val memory = [0x12345678, 0xDEADBEEF]
expect(mem_load(memory, 0, MemWidth.Word, false)).to_equal(0x12345678)
expect(mem_load(memory, 4, MemWidth.Word, false)).to_equal(0xDEADBEEF)
```

</details>

#### loads a byte with sign extension

- loads a byte with sign extension
   - Expected: mem_load(memory, 0, MemWidth.Byte, true) equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("loads a byte with sign extension")
val memory = [0x000000FF]
expect(mem_load(memory, 0, MemWidth.Byte, true)).to_equal(0xFFFFFFFF)
```

</details>

#### loads a byte without sign extension

- loads a byte without sign extension
   - Expected: mem_load(memory, 0, MemWidth.Byte, false) equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("loads a byte without sign extension")
val memory = [0x000000FF]
expect(mem_load(memory, 0, MemWidth.Byte, false)).to_equal(0xFF)
```

</details>

#### stores a word to memory

- stores a word to memory
   - Expected: updated[0] equals `0xCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores a word to memory")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-RV32IMAC`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `52435ce7602bc1f963e3e0b0df474c8c3df4ee69826b3d6791cf9e0009795860`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `52435ce7602bc1f963e3e0b0df474c8c3df4ee69826b3d6791cf9e0009795860`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `52435ce7602bc1f963e3e0b0df474c8c3df4ee69826b3d6791cf9e0009795860`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl
mirror: doc/06_spec/02_integration/hardware/rv32imac/rv32_core_smoke_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/02_integration/hardware/rv32imac/rv32_core_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/hardware/rv32imac/rv32_core_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x0 always reads as zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes and reads back correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/hardware/rv32imac/rv32_core_smoke_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles all 32 registers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
