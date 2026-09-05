# RV64 Baremetal OS Boot Integration Test

> Purpose: This spec proves RV64 Boot — Reset Vector.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Baremetal OS Boot Integration Test

Purpose: This spec proves RV64 Boot — Reset Vector.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-BOOT-001 |
| Category | OS |
| Difficulty | 4/5 |
| Status | Draft |
| Source | `test/integration/os/rv64_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves RV64 Boot — Reset Vector.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### RV64 Boot — Reset Vector

#### PC starts at DRAM_BASE (0x80000000)

- PC starts at DRAM_BASE (0x80000000)
   - Expected: reset_pc equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RV64BOOT-001
step("PC starts at DRAM_BASE (0x80000000)")
val reset_pc: i64 = DRAM_BASE
expect(reset_pc).to_equal(0x80000000)
```

</details>

#### all registers zero at reset

- all registers zero at reset
- all registers zero at reset
   - Expected: all_zero is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("all registers zero at reset")
step("all registers zero at reset")
val rf = Rv64RegFile.create()
var i = 0
var all_zero = true
while i < 32:
    if rf.read(i) != 0:
        all_zero = false
    i = i + 1
expect(all_zero).to_equal(true)
```

</details>

#### x0 stays zero after attempted write

- x0 stays zero after attempted write
- x0 stays zero after attempted write
   - Expected: rf.read(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("x0 stays zero after attempted write")
step("x0 stays zero after attempted write")
var rf = Rv64RegFile.create()
rf.write(0, 0xDEAD)
expect(rf.read(0)).to_equal(0)
```

</details>

### RV64 Boot — RAM Load and Execute

#### load instruction bytes to RAM

- load instruction bytes to RAM
- load instruction bytes to RAM
   - Expected: ram.read32(0).value equals `0x02A00513`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("load instruction bytes to RAM")
step("load instruction bytes to RAM")
var ram = Rv64Ram.create(64)
# ADDI x10, x0, 42 = 0x02A00513
ram.write32(0, 0x02A00513)
expect(ram.read32(0).value).to_equal(0x02A00513)
```

</details>

#### fetch and decode ADDI from RAM

- fetch and decode ADDI from RAM
- fetch and decode ADDI from RAM
   - Expected: opcode equals `OP_OP_IMM`
   - Expected: rd equals `10`
   - Expected: rs1 equals `0`
   - Expected: imm equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fetch and decode ADDI from RAM")
step("fetch and decode ADDI from RAM")
var ram = Rv64Ram.create(64)
ram.write32(0, 0x02A00513)  # ADDI x10, x0, 42
val instr = ram.read32(0).value
val opcode = decode_opcode(instr)
val rd = decode_rd(instr)
val rs1 = decode_rs1(instr)
val imm = decode_imm_i(instr)
expect(opcode).to_equal(OP_OP_IMM)
expect(rd).to_equal(10)
expect(rs1).to_equal(0)
expect(imm).to_equal(42)
```

</details>

#### execute ADDI and writeback to register

- execute ADDI and writeback to register
- execute ADDI and writeback to register
   - Expected: rf.read(10) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("execute ADDI and writeback to register")
step("execute ADDI and writeback to register")
var rf = Rv64RegFile.create()
var ram = Rv64Ram.create(64)
ram.write32(0, 0x02A00513)  # ADDI x10, x0, 42
val instr = ram.read32(0).value
val rd = decode_rd(instr) + 0
val rs1_idx = decode_rs1(instr) + 0
val rs1_val = rf.read(rs1_idx)
val imm = decode_imm_i(instr)
val result = alu_execute(AluOp.Add, rs1_val, imm)
rf.write(rd, result)
expect(rf.read(10)).to_equal(42)
```

</details>

#### multi-instruction program: compute 3+4

- multi-instruction program: compute 3+4
- multi-instruction program: compute 3+4
   - Expected: rf.read(10) equals `3`
   - Expected: rf.read(11) equals `4`
   - Expected: rf.read(12) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("multi-instruction program: compute 3+4")
step("multi-instruction program: compute 3+4")
var rf = Rv64RegFile.create()
var ram = Rv64Ram.create(64)
# ADDI x10, x0, 3 = 0x00300513
# ADDI x11, x0, 4 = 0x00400593
# ADD  x12, x10, x11 = 0x00B50633
ram.write32(0, 0x00300513)
ram.write32(4, 0x00400593)
ram.write32(8, 0x00B50633)

# Execute instruction 1: ADDI x10, x0, 3
var instr = ram.read32(0).value
val rd1 = decode_rd(instr) + 0
val rs1_idx = decode_rs1(instr) + 0
val imm1 = decode_imm_i(instr)
rf.write(rd1, alu_execute(AluOp.Add, rf.read(rs1_idx), imm1))
expect(rf.read(10)).to_equal(3)

# Execute instruction 2: ADDI x11, x0, 4
instr = ram.read32(4).value
val rd2 = decode_rd(instr) + 0
val rs2_idx_imm = decode_rs1(instr) + 0
val imm2 = decode_imm_i(instr)
rf.write(rd2, alu_execute(AluOp.Add, rf.read(rs2_idx_imm), imm2))
expect(rf.read(11)).to_equal(4)

# Execute instruction 3: ADD x12, x10, x11
instr = ram.read32(8).value
val rs1_idx_add = decode_rs1(instr) + 0
val rs2_idx_add = decode_rs2(instr) + 0
val rd3 = decode_rd(instr) + 0
val rs1 = rf.read(rs1_idx_add)
val rs2 = rf.read(rs2_idx_add)
rf.write(rd3, alu_execute(AluOp.Add, rs1, rs2))
expect(rf.read(12)).to_equal(7)
```

</details>

### RV64 Boot — Store and Load Cycle

#### store word then load word

- store word then load word
- store word then load word
   - Expected: loaded equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("store word then load word")
step("store word then load word")
var ram = Rv64Ram.create(256)
# Store 0xDEADBEEF at address 128
ram.write32(128, 0xDEADBEEF)
# Load from address 128
val loaded = ram.read32(128).value
expect(loaded).to_equal(0xDEADBEEF)
```

</details>

#### store double then load double

- store double then load double
- store double then load double
   - Expected: ram.read64(128).value equals `0xCAFEBABEDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("store double then load double")
step("store double then load double")
var ram = Rv64Ram.create(256)
ram.write64(128, 0xCAFEBABEDEADBEEF)
expect(ram.read64(128).value).to_equal(0xCAFEBABEDEADBEEF)
```

</details>

#### store byte then load byte with sign extension

- store byte then load byte with sign extension
- store byte then load byte with sign extension
   - Expected: sign_ext equals `0xFFFFFFFFFFFFFF80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("store byte then load byte with sign extension")
step("store byte then load byte with sign extension")
var ram = Rv64Ram.create(256)
ram.write8(128, 0x80)
val raw = ram.read8(128).value
# Simulate LB sign extension
val sign_ext = if (raw and 0x80) != 0: raw or 0xFFFFFFFFFFFFFF00 else: raw
expect(sign_ext).to_equal(0xFFFFFFFFFFFFFF80)
```

</details>

### RV64 Boot — UART Output Simulation

#### write 'H' to UART address

- write 'H' to UART address
- write 'H' to UART address
   - Expected: uart_buffer[0] equals `0x48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write 'H' to UART address")
step("write 'H' to UART address")
var uart_buffer: [i64] = []
val ch: i64 = 0x48  # 'H'
uart_buffer = uart_buffer + [ch]
expect(uart_buffer[0]).to_equal(0x48)
```

</details>

#### write 'Hello' byte-by-byte

- write 'Hello' byte-by-byte
- write 'Hello' byte-by-byte
   - Expected: uart_buffer.len() equals `5`
   - Expected: uart_buffer[0] equals `0x48`
   - Expected: uart_buffer[4] equals `0x6F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write 'Hello' byte-by-byte")
step("write 'Hello' byte-by-byte")
var uart_buffer: [i64] = []
uart_buffer.push(0x48)
uart_buffer.push(0x65)
uart_buffer.push(0x6C)
uart_buffer.push(0x6C)
uart_buffer.push(0x6F)
expect(uart_buffer.len()).to_equal(5)
expect(uart_buffer[0]).to_equal(0x48)
expect(uart_buffer[4]).to_equal(0x6F)
```

</details>

#### UART THR at offset 0 from UART_BASE

- UART THR at offset 0 from UART_BASE
- UART THR at offset 0 from UART_BASE
   - Expected: thr_addr equals `0x10000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("UART THR at offset 0 from UART_BASE")
step("UART THR at offset 0 from UART_BASE")
val thr_addr = UART_BASE + 0
expect(thr_addr).to_equal(0x10000000)
```

</details>

#### UART LSR at offset 5 — TX ready check

- UART LSR at offset 5 — TX ready check
- UART LSR at offset 5 — TX ready check
   - Expected: tx_ready is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("UART LSR at offset 5 — TX ready check")
step("UART LSR at offset 5 — TX ready check")
val lsr_addr = UART_BASE + 5
val lsr_val: i64 = 0x60  # THR empty + transmitter idle
val tx_ready = (lsr_val and 0x20) != 0
expect(tx_ready).to_equal(true)
```

</details>

### RV64 Boot — Stack Setup

#### set SP to top of 128MB RAM

- set SP to top of 128MB RAM
- set SP to top of 128MB RAM
   - Expected: rf.read(2) equals `0x88000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("set SP to top of 128MB RAM")
step("set SP to top of 128MB RAM")
var rf = Rv64RegFile.create()
val stack_top = DRAM_BASE + 0x8000000  # 128MB
rf.write(2, stack_top)
expect(rf.read(2)).to_equal(0x88000000)
```

</details>

#### stack push/pop simulation

- stack push/pop simulation
- stack push/pop simulation
   - Expected: loaded equals `0xCAFEBABE`
   - Expected: rf.read(2) equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stack push/pop simulation")
step("stack push/pop simulation")
var rf = Rv64RegFile.create()
var ram = Rv64Ram.create(256)
rf.write(2, 256)  # SP = 256

# Push: SP -= 8, store value
val sp = rf.read(2) - 8
rf.write(2, sp)
ram.write64(sp, 0xCAFEBABE)

# Pop: load value, SP += 8
val loaded = ram.read64(rf.read(2)).value
rf.write(2, rf.read(2) + 8)

expect(loaded).to_equal(0xCAFEBABE)
expect(rf.read(2)).to_equal(256)
```

</details>

### RV64 Boot — W-Variant in Boot Code

#### ADDIW for 32-bit counter

- ADDIW for 32-bit counter
- ADDIW for 32-bit counter
   - Expected: rf.read(10) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ADDIW for 32-bit counter")
step("ADDIW for 32-bit counter")
var rf = Rv64RegFile.create()
rf.write(10, 0)
# Loop counter increment with ADDIW
val result = alu_execute_word(AluOp.Addw, rf.read(10), 1)
rf.write(10, result)
expect(rf.read(10)).to_equal(1)
```

</details>

#### ADDW for 32-bit address calculation

- ADDW for 32-bit address calculation
- ADDW for 32-bit address calculation
   - Expected: result equals `0x10000100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ADDW for 32-bit address calculation")
step("ADDW for 32-bit address calculation")
val base: i64 = 0x10000000
val offset: i64 = 0x100
val result = alu_execute_word(AluOp.Addw, base, offset)
expect(result).to_equal(0x10000100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-RV64BOOT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `603ca74a9b2dafba851ec2e0ffa168389665a6533038f26cd77208dcff508b39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `603ca74a9b2dafba851ec2e0ffa168389665a6533038f26cd77208dcff508b39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `603ca74a9b2dafba851ec2e0ffa168389665a6533038f26cd77208dcff508b39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/os/rv64_boot_spec.spl
mirror: doc/06_spec/integration/os/rv64_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/os/rv64_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/os/rv64_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/os/rv64_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/os/rv64_boot_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PC starts at DRAM_BASE (0x80000000)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/rv64_boot_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all registers zero at reset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/rv64_boot_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'x0 stays zero after attempted write' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
