# Rv32imac Specification

> <details>

<!-- sdn-diagram:id=rv32imac_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32imac_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32imac_spec -> spipe
rv32imac_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32imac_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_decode_opcode(0x00A00513)).to_equal(OP_OP_IMM)
```

</details>

#### extracts rd correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_decode_rd(0x00A00513)).to_equal(10)
```

</details>

#### extracts rs1 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_decode_rs1(0x00A00513)).to_equal(0)
```

</details>

#### extracts funct3 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_decode_funct3(0x00A00513)).to_equal(0)
```

</details>

#### decodes I-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_decode_imm_i(0x00A00513)).to_equal(10)
```

</details>

#### decodes negative I-type immediate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_decode_imm_i(0xFFB00513) + 4294967296).to_equal(0xFFFFFFFB)
```

</details>

#### decodes R-type ALU operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_decode_alu_op(OP_OP, F3_ADD_SUB, F7_NORMAL) == AluOp.Add).to_equal(true)
```

</details>

#### distinguishes ADD from SUB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_decode_alu_op(OP_OP, F3_ADD_SUB, F7_NORMAL) == AluOp.Add).to_equal(true)
expect(rv32_decode_alu_op(OP_OP, F3_ADD_SUB, F7_SUB_SRA) == AluOp.Sub).to_equal(true)
```

</details>

#### detects RVC instructions and compressed register aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed(0x0512)).to_equal(true)
expect(rvc_reg(2)).to_equal(10)
```

</details>

#### pipeline hazards

#### detects load-use hazard

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_detect_load_use_hazard(5, 0, 5, MemOp.Load, true)).to_equal(true)
```

</details>

#### no hazard when EX is not a load

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_detect_load_use_hazard(5, 0, 5, MemOp.None_, true)).to_equal(false)
```

</details>

#### no hazard when rd is x0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_detect_load_use_hazard(0, 3, 0, MemOp.Load, true)).to_equal(false)
```

</details>

#### forwards from EX to ID

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_resolve_forward_rs1(5, 5, true, 0, false) == ForwardSrc.FromEx).to_equal(true)
```

</details>

#### forwards from MEM to ID when EX does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_resolve_forward_rs1(5, 3, true, 5, true) == ForwardSrc.FromMem).to_equal(true)
```

</details>

#### stalls on load-use hazard

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = rv32_pipeline_control(true, false, false)
expect(ctrl.stall_if).to_equal(true)
expect(ctrl.stall_id).to_equal(true)
expect(ctrl.flush_ex).to_equal(true)
```

</details>

#### flushes on taken branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = rv32_pipeline_control(false, true, false)
expect(ctrl.flush_if).to_equal(true)
expect(ctrl.flush_id).to_equal(true)
```

</details>

#### CSR operations

#### reads and writes mstatus correctly

1. var csr = create rv32 csr file
2. csr write
   - Expected: csr.read(CSR_MSTATUS) equals `0x00001808`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = create_rv32_csr_file()
csr.write(CSR_MSTATUS, 0x00001808)
expect(csr.read(CSR_MSTATUS)).to_equal(0x00001808)
```

</details>

#### reads misa correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr = create_rv32_csr_file()
expect(csr.read(CSR_MISA)).to_equal(0x40101104)
```

</details>

#### handles CSRRW

1. var csr = create rv32 csr file
2. csr write
   - Expected: csr.csrrw(CSR_MSCRATCH, 0xDEADBEEF) equals `0x12345678`
   - Expected: csr.read(CSR_MSCRATCH) equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = create_rv32_csr_file()
csr.write(CSR_MSCRATCH, 0x12345678)
expect(csr.csrrw(CSR_MSCRATCH, 0xDEADBEEF)).to_equal(0x12345678)
expect(csr.read(CSR_MSCRATCH)).to_equal(0xDEADBEEF)
```

</details>

#### handles CSRRS

1. var csr = create rv32 csr file
   - Expected: csr.csrrs(CSR_MIE, 0x80) equals `0`
   - Expected: csr.read(CSR_MIE) equals `0x80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = create_rv32_csr_file()
expect(csr.csrrs(CSR_MIE, 0x80)).to_equal(0)
expect(csr.read(CSR_MIE)).to_equal(0x80)
```

</details>

#### handles CSRRC

1. var csr = create rv32 csr file
2. csr write
   - Expected: csr.csrrc(CSR_MIE, 0x80) equals `0xFF`
   - Expected: csr.read(CSR_MIE) equals `0x7F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = create_rv32_csr_file()
csr.write(CSR_MIE, 0xFF)
expect(csr.csrrc(CSR_MIE, 0x80)).to_equal(0xFF)
expect(csr.read(CSR_MIE)).to_equal(0x7F)
```

</details>

#### handles ECALL trap

1. var csr = create rv32 csr file
2. csr write
3. csr trap enter
   - Expected: csr.read(CSR_MEPC) equals `0x80001000`
   - Expected: csr.read(CSR_MCAUSE) equals `11`
   - Expected: csr.trap_vector() equals `0x80000100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = create_rv32_csr_file()
csr.write(CSR_MTVEC, 0x80000100)
csr.trap_enter(11, 0x80001000, 0)
expect(csr.read(CSR_MEPC)).to_equal(0x80001000)
expect(csr.read(CSR_MCAUSE)).to_equal(11)
expect(csr.trap_vector()).to_equal(0x80000100)
```

</details>

#### returns from trap via mret

1. var csr = create rv32 csr file
2. csr write
3. csr trap enter
   - Expected: csr.trap_return() equals `0x80001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = create_rv32_csr_file()
csr.write(CSR_MTVEC, 0x80000100)
csr.trap_enter(11, 0x80001000, 0)
expect(csr.trap_return()).to_equal(0x80001000)
```

</details>

#### M extension

#### computes MUL correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_muldiv_execute("mul", 12, 13)).to_equal(156)
```

</details>

#### handles division by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_muldiv_execute("div", 42, 0)).to_equal(0xFFFFFFFF)
```

</details>

#### handles signed division overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv32_muldiv_execute("div", 0x80000000, 0xFFFFFFFF)).to_equal(0x80000000)
```

</details>

#### A extension

#### LR/SC succeeds on uncontested reservation

1. var rs = create rv32 reservation set
2. rs reserve
   - Expected: rs.check_and_clear(0x80000000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rs = create_rv32_reservation_set()
rs.reserve(0x80000000)
expect(rs.check_and_clear(0x80000000)).to_equal(true)
```

</details>

#### SC fails after intervening store

1. var rs = create rv32 reservation set
2. rs reserve
3. rs invalidate if match
   - Expected: rs.check_and_clear(0x80000000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rs = create_rv32_reservation_set()
rs.reserve(0x80000000)
rs.invalidate_if_match(0x80000000)
expect(rs.check_and_clear(0x80000000)).to_equal(false)
```

</details>

#### SC fails on address mismatch

1. var rs = create rv32 reservation set
2. rs reserve
   - Expected: rs.check_and_clear(0x80000004) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
