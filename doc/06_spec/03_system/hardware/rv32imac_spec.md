# Rv32imac Specification

> Tests covering RV32IMAC Processor.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv32imac Specification

## Scenarios

### RV32IMAC Processor

#### instruction decode

#### extracts opcode correctly

- extracts opcode correctly
   - Expected: rv32_decode_opcode(0x00A00513) equals `OP_OP_IMM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts opcode correctly")
expect(rv32_decode_opcode(0x00A00513)).to_equal(OP_OP_IMM)
```

</details>

#### extracts rd correctly

- extracts rd correctly
   - Expected: rv32_decode_rd(0x00A00513) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts rd correctly")
expect(rv32_decode_rd(0x00A00513)).to_equal(10)
```

</details>

#### extracts rs1 correctly

- extracts rs1 correctly
   - Expected: rv32_decode_rs1(0x00A00513) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts rs1 correctly")
expect(rv32_decode_rs1(0x00A00513)).to_equal(0)
```

</details>

#### extracts funct3 correctly

- extracts funct3 correctly
   - Expected: rv32_decode_funct3(0x00A00513) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts funct3 correctly")
expect(rv32_decode_funct3(0x00A00513)).to_equal(0)
```

</details>

#### decodes I-type immediate

- decodes I-type immediate
   - Expected: rv32_decode_imm_i(0x00A00513) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decodes I-type immediate")
expect(rv32_decode_imm_i(0x00A00513)).to_equal(10)
```

</details>

#### decodes negative I-type immediate

- decodes negative I-type immediate
   - Expected: rv32_decode_imm_i(0xFFB00513) + 4294967296 equals `0xFFFFFFFB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decodes negative I-type immediate")
expect(rv32_decode_imm_i(0xFFB00513) + 4294967296).to_equal(0xFFFFFFFB)
```

</details>

#### decodes R-type ALU operation

- decodes R-type ALU operation
   - Expected: rv32_decode_alu_op(OP_OP, F3_ADD_SUB, F7_NORMAL) equals `AluOp.Add`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decodes R-type ALU operation")
expect(rv32_decode_alu_op(OP_OP, F3_ADD_SUB, F7_NORMAL)).to_equal(AluOp.Add)
```

</details>

#### distinguishes ADD from SUB

- distinguishes ADD from SUB
   - Expected: rv32_decode_alu_op(OP_OP, F3_ADD_SUB, F7_NORMAL) equals `AluOp.Add`
   - Expected: rv32_decode_alu_op(OP_OP, F3_ADD_SUB, F7_SUB_SRA) equals `AluOp.Sub`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("distinguishes ADD from SUB")
expect(rv32_decode_alu_op(OP_OP, F3_ADD_SUB, F7_NORMAL)).to_equal(AluOp.Add)
expect(rv32_decode_alu_op(OP_OP, F3_ADD_SUB, F7_SUB_SRA)).to_equal(AluOp.Sub)
```

</details>

#### detects RVC instructions and compressed register aliases

- detects RVC instructions and compressed register aliases
   - Expected: is_compressed(0x0512) is true
   - Expected: rvc_reg(2) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects RVC instructions and compressed register aliases")
expect(is_compressed(0x0512)).to_equal(true)
expect(rvc_reg(2)).to_equal(10)
```

</details>

#### pipeline hazards

#### detects load-use hazard

- detects load-use hazard
   - Expected: rv32_detect_load_use_hazard(5, 0, 5, MemOp.Load, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects load-use hazard")
expect(rv32_detect_load_use_hazard(5, 0, 5, MemOp.Load, true)).to_equal(true)
```

</details>

#### no hazard when EX is not a load

- no hazard when EX is not a load
   - Expected: rv32_detect_load_use_hazard(5, 0, 5, MemOp.None_, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no hazard when EX is not a load")
expect(rv32_detect_load_use_hazard(5, 0, 5, MemOp.None_, true)).to_equal(false)
```

</details>

#### no hazard when rd is x0

- no hazard when rd is x0
   - Expected: rv32_detect_load_use_hazard(0, 3, 0, MemOp.Load, true) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no hazard when rd is x0")
expect(rv32_detect_load_use_hazard(0, 3, 0, MemOp.Load, true)).to_equal(false)
```

</details>

#### forwards from EX to ID

- forwards from EX to ID
   - Expected: rv32_resolve_forward_rs1(5, 5, true, 0, false) equals `ForwardSrc.FromEx`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forwards from EX to ID")
expect(rv32_resolve_forward_rs1(5, 5, true, 0, false)).to_equal(ForwardSrc.FromEx)
```

</details>

#### forwards from MEM to ID when EX does not match

- forwards from MEM to ID when EX does not match
   - Expected: rv32_resolve_forward_rs1(5, 3, true, 5, true) equals `ForwardSrc.FromMem`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("forwards from MEM to ID when EX does not match")
expect(rv32_resolve_forward_rs1(5, 3, true, 5, true)).to_equal(ForwardSrc.FromMem)
```

</details>

#### stalls on load-use hazard

- stalls on load-use hazard
   - Expected: ctrl.stall_if is true
   - Expected: ctrl.stall_id is true
   - Expected: ctrl.flush_ex is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stalls on load-use hazard")
val ctrl = rv32_pipeline_control(true, false, false)
expect(ctrl.stall_if).to_equal(true)
expect(ctrl.stall_id).to_equal(true)
expect(ctrl.flush_ex).to_equal(true)
```

</details>

#### flushes on taken branch

- flushes on taken branch
   - Expected: ctrl.flush_if is true
   - Expected: ctrl.flush_id is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flushes on taken branch")
val ctrl = rv32_pipeline_control(false, true, false)
expect(ctrl.flush_if).to_equal(true)
expect(ctrl.flush_id).to_equal(true)
```

</details>

#### CSR operations

#### reads and writes mstatus correctly

- reads and writes mstatus correctly
   - Expected: csr.read(CSR_MSTATUS) equals `0x00001808`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads and writes mstatus correctly")
var csr = create_rv32_csr_file()
csr.write(CSR_MSTATUS, 0x00001808)
expect(csr.read(CSR_MSTATUS)).to_equal(0x00001808)
```

</details>

#### reads misa correctly

- reads misa correctly
   - Expected: csr.read(CSR_MISA) equals `0x40101104`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads misa correctly")
val csr = create_rv32_csr_file()
expect(csr.read(CSR_MISA)).to_equal(0x40101104)
```

</details>

#### handles CSRRW

- handles CSRRW
   - Expected: csr.csrrw(CSR_MSCRATCH, 0xDEADBEEF) equals `0x12345678`
   - Expected: csr.read(CSR_MSCRATCH) equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles CSRRW")
var csr = create_rv32_csr_file()
csr.write(CSR_MSCRATCH, 0x12345678)
expect(csr.csrrw(CSR_MSCRATCH, 0xDEADBEEF)).to_equal(0x12345678)
expect(csr.read(CSR_MSCRATCH)).to_equal(0xDEADBEEF)
```

</details>

#### handles CSRRS

- handles CSRRS
   - Expected: csr.csrrs(CSR_MIE, 0x80) equals `0`
   - Expected: csr.read(CSR_MIE) equals `0x80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles CSRRS")
var csr = create_rv32_csr_file()
expect(csr.csrrs(CSR_MIE, 0x80)).to_equal(0)
expect(csr.read(CSR_MIE)).to_equal(0x80)
```

</details>

#### handles CSRRC

- handles CSRRC
   - Expected: csr.csrrc(CSR_MIE, 0x80) equals `0xFF`
   - Expected: csr.read(CSR_MIE) equals `0x7F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles CSRRC")
var csr = create_rv32_csr_file()
csr.write(CSR_MIE, 0xFF)
expect(csr.csrrc(CSR_MIE, 0x80)).to_equal(0xFF)
expect(csr.read(CSR_MIE)).to_equal(0x7F)
```

</details>

#### handles ECALL trap

- handles ECALL trap
   - Expected: csr.read(CSR_MEPC) equals `0x80001000`
   - Expected: csr.read(CSR_MCAUSE) equals `11`
   - Expected: csr.trap_vector() equals `0x80000100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles ECALL trap")
var csr = create_rv32_csr_file()
csr.write(CSR_MTVEC, 0x80000100)
csr.trap_enter(11, 0x80001000, 0)
expect(csr.read(CSR_MEPC)).to_equal(0x80001000)
expect(csr.read(CSR_MCAUSE)).to_equal(11)
expect(csr.trap_vector()).to_equal(0x80000100)
```

</details>

#### returns from trap via mret

- returns from trap via mret
   - Expected: csr.trap_return() equals `0x80001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns from trap via mret")
var csr = create_rv32_csr_file()
csr.write(CSR_MTVEC, 0x80000100)
csr.trap_enter(11, 0x80001000, 0)
expect(csr.trap_return()).to_equal(0x80001000)
```

</details>

#### M extension

#### computes MUL correctly

- computes MUL correctly
   - Expected: rv32_muldiv_execute("mul", 12, 13) equals `156`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes MUL correctly")
expect(rv32_muldiv_execute("mul", 12, 13)).to_equal(156)
```

</details>

#### handles division by zero

- handles division by zero
   - Expected: rv32_muldiv_execute("div", 42, 0) equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles division by zero")
expect(rv32_muldiv_execute("div", 42, 0)).to_equal(0xFFFFFFFF)
```

</details>

#### handles signed division overflow

- handles signed division overflow
   - Expected: rv32_muldiv_execute("div", 0x80000000, 0xFFFFFFFF) equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles signed division overflow")
expect(rv32_muldiv_execute("div", 0x80000000, 0xFFFFFFFF)).to_equal(0x80000000)
```

</details>

#### A extension

#### LR/SC succeeds on uncontested reservation

- LR/SC succeeds on uncontested reservation
   - Expected: rs.check_and_clear(0x80000000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("LR/SC succeeds on uncontested reservation")
var rs = create_rv32_reservation_set()
rs.reserve(0x80000000)
expect(rs.check_and_clear(0x80000000)).to_equal(true)
```

</details>

#### SC fails after intervening store

- SC fails after intervening store
   - Expected: rs.check_and_clear(0x80000000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SC fails after intervening store")
var rs = create_rv32_reservation_set()
rs.reserve(0x80000000)
rs.invalidate_if_match(0x80000000)
expect(rs.check_and_clear(0x80000000)).to_equal(false)
```

</details>

#### SC fails on address mismatch

- SC fails on address mismatch
   - Expected: rs.check_and_clear(0x80000004) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SC fails on address mismatch")
var rs = create_rv32_reservation_set()
rs.reserve(0x80000000)
expect(rs.check_and_clear(0x80000004)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/rv32imac_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV32IMAC Processor.
- RV32IMAC Processor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-RV32IMAC`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `710a30258424b2f722c0367171360af98d6c144d323cf304899376fdf137b914`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `710a30258424b2f722c0367171360af98d6c144d323cf304899376fdf137b914`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `710a30258424b2f722c0367171360af98d6c144d323cf304899376fdf137b914`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/hardware/rv32imac_spec.spl
mirror: doc/06_spec/03_system/hardware/rv32imac_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/hardware/rv32imac_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/rv32imac_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/rv32imac_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/hardware/rv32imac_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/hardware/rv32imac_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts opcode correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/rv32imac_spec.spl:179:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts rd correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/rv32imac_spec.spl:184:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts rs1 correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
