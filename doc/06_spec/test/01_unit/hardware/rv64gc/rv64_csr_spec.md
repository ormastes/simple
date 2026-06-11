# RV64 CSR Unit Tests

> Unit tests for 64-bit Control and Status Register file operations. Covers M-mode, S-mode, and FP CSRs.

<!-- sdn-diagram:id=rv64_csr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_csr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_csr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_csr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 CSR Unit Tests

Unit tests for 64-bit Control and Status Register file operations. Covers M-mode, S-mode, and FP CSRs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-CSR-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/hardware/rv64gc/rv64_csr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for 64-bit Control and Status Register file operations.
Covers M-mode, S-mode, and FP CSRs.

## Scenarios

### CSR Read/Write

#### reads misa with RV64GC configuration

1. var csr =  create csr
   - Expected: (misa >> 62) and 0x3 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
val misa = csr.read(CSR_MISA)
# Check MXL = 2 (bits 63:62)
expect((misa >> 62) and 0x3).to_equal(2)
```

</details>

#### writes and reads mscratch

1. var csr =  create csr
2. csr write
   - Expected: csr.read(CSR_MSCRATCH) equals `0xDEADBEEFCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MSCRATCH, 0xDEADBEEFCAFEBABE)
expect(csr.read(CSR_MSCRATCH)).to_equal(0xDEADBEEFCAFEBABE)
```

</details>

#### mepc aligns to 2-byte boundary

1. var csr =  create csr
2. csr write
   - Expected: csr.read(CSR_MEPC) equals `0x80000002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MEPC, 0x80000003)
expect(csr.read(CSR_MEPC)).to_equal(0x80000002)
```

</details>

#### writes and reads S-mode CSRs

1. var csr =  create csr
2. csr write
   - Expected: csr.read(CSR_SSCRATCH) equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_SSCRATCH, 0x12345678)
expect(csr.read(CSR_SSCRATCH)).to_equal(0x12345678)
```

</details>

### CSRRW Operation

#### CSRRW returns old value and writes new

1. var csr =  create csr
2. csr write
   - Expected: old equals `100`
   - Expected: csr.read(CSR_MSCRATCH) equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MSCRATCH, 100)
val old = csr.csrrw(CSR_MSCRATCH, 200)
expect(old).to_equal(100)
expect(csr.read(CSR_MSCRATCH)).to_equal(200)
```

</details>

#### CSRRW with zero source

1. var csr =  create csr
2. csr write
   - Expected: old equals `42`
   - Expected: csr.read(CSR_MSCRATCH) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MSCRATCH, 42)
val old = csr.csrrw(CSR_MSCRATCH, 0)
expect(old).to_equal(42)
expect(csr.read(CSR_MSCRATCH)).to_equal(0)
```

</details>

### CSRRS Operation

#### CSRRS sets bits

1. var csr =  create csr
2. csr write
   - Expected: old equals `0x0F`
   - Expected: csr.read(CSR_MIE) equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MIE, 0x0F)
val old = csr.csrrs(CSR_MIE, 0xF0)
expect(old).to_equal(0x0F)
expect(csr.read(CSR_MIE)).to_equal(0xFF)
```

</details>

#### CSRRS with rs1=0 is read-only

1. var csr =  create csr
2. csr write
   - Expected: old equals `0x0F`
   - Expected: csr.read(CSR_MIE) equals `0x0F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MIE, 0x0F)
val old = csr.csrrs(CSR_MIE, 0)
expect(old).to_equal(0x0F)
expect(csr.read(CSR_MIE)).to_equal(0x0F)
```

</details>

### CSRRC Operation

#### CSRRC clears bits

1. var csr =  create csr
2. csr write
   - Expected: old equals `0xFF`
   - Expected: csr.read(CSR_MIE) equals `0xF0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MIE, 0xFF)
val old = csr.csrrc(CSR_MIE, 0x0F)
expect(old).to_equal(0xFF)
expect(csr.read(CSR_MIE)).to_equal(0xF0)
```

</details>

#### CSRRC with rs1=0 is read-only

1. var csr =  create csr
2. csr write
   - Expected: old equals `0xFF`
   - Expected: csr.read(CSR_MIE) equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MIE, 0xFF)
val old = csr.csrrc(CSR_MIE, 0)
expect(old).to_equal(0xFF)
expect(csr.read(CSR_MIE)).to_equal(0xFF)
```

</details>

### Trap Entry/Return

#### trap_enter saves cause, tval, pc

1. var csr =  create csr
2. csr trap enter
   - Expected: csr.read(CSR_MCAUSE) equals `11`
   - Expected: csr.read(CSR_MTVAL) equals `0xDEAD`
   - Expected: csr.read(CSR_MEPC) equals `0x80001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.trap_enter(11, 0xDEAD, 0x80001000)
expect(csr.read(CSR_MCAUSE)).to_equal(11)
expect(csr.read(CSR_MTVAL)).to_equal(0xDEAD)
expect(csr.read(CSR_MEPC)).to_equal(0x80001000)
```

</details>

#### trap_return restores MPIE to MIE

1. var csr =  create csr
2. csr write
3. csr write
4. csr trap enter
   - Expected: return_pc equals `0x80001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
# Set MIE=1 (bit 3)
csr.write(CSR_MSTATUS, 0x8)
csr.write(CSR_MEPC, 0x80002000)
csr.trap_enter(2, 0, 0x80001000)
val return_pc = csr.trap_return()
expect(return_pc).to_equal(0x80001000)
```

</details>

### Performance Counters

#### tick increments mcycle

1. var csr =  create csr
2. csr tick
3. csr tick
   - Expected: csr.read(CSR_MCYCLE) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.tick()
csr.tick()
expect(csr.read(CSR_MCYCLE)).to_equal(2)
```

</details>

#### retire increments minstret

1. var csr =  create csr
2. csr retire
   - Expected: csr.read(CSR_MINSTRET) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.retire()
expect(csr.read(CSR_MINSTRET)).to_equal(1)
```

</details>

### S-Mode CSR Views

#### sstatus is a filtered view of mstatus

1. var csr =  create csr
2. csr write
   - Expected: sstatus equals `0xFFFFFFFFFFFFFFFF and 0x800DE133`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MSTATUS, 0xFFFFFFFFFFFFFFFF)
val sstatus = csr.read(CSR_SSTATUS)
# sstatus only exposes specific bits
expect(sstatus).to_equal(0xFFFFFFFFFFFFFFFF and 0x800DE133)
```

</details>

#### sie filters mie through mideleg

1. var csr =  create csr
2. csr write
3. csr write
   - Expected: csr.read(CSR_SIE) equals `0x0F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MIE, 0xFF)
csr.write(CSR_MIDELEG, 0x0F)
expect(csr.read(CSR_SIE)).to_equal(0x0F)
```

</details>

#### satp stores Sv39 mode and PPN

1. var csr =  create csr
2. csr write
   - Expected: csr.read(CSR_SATP) equals `satp_val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
# Sv39 mode = 8 (bits 63:60), ASID = 0, PPN
val satp_val = (8 << 60) or 0x80000
csr.write(CSR_SATP, satp_val)
expect(csr.read(CSR_SATP)).to_equal(satp_val)
```

</details>

### FP CSRs

#### fflags reads lower 5 bits of fcsr

1. var csr =  create csr
2. csr write
   - Expected: csr.read(CSR_FFLAGS) equals `0x1F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_FCSR, 0xFF)
expect(csr.read(CSR_FFLAGS)).to_equal(0x1F)
```

</details>

#### frm reads bits 7:5 of fcsr

1. var csr =  create csr
2. csr write
   - Expected: csr.read(CSR_FRM) equals `0x7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_FCSR, 0xE0)
expect(csr.read(CSR_FRM)).to_equal(0x7)
```

</details>

#### writing fflags preserves frm

1. var csr =  create csr
2. csr write
3. csr write
   - Expected: csr.read(CSR_FCSR) equals `0xF5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_FCSR, 0xE0)
csr.write(CSR_FFLAGS, 0x15)
expect(csr.read(CSR_FCSR)).to_equal(0xF5)
```

</details>

#### writing frm preserves fflags

1. var csr =  create csr
2. csr write
3. csr write
   - Expected: csr.read(CSR_FCSR) equals `0xBF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_FCSR, 0x1F)
csr.write(CSR_FRM, 0x5)
expect(csr.read(CSR_FCSR)).to_equal(0xBF)
```

</details>

### CSR Immediate Operations

#### CSRRWI: writes immediate, returns old

1. var csr =  create csr
2. csr write
   - Expected: old equals `42`
   - Expected: csr.read(CSR_MSCRATCH) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MSCRATCH, 42)
val old = csr.csrrw(CSR_MSCRATCH, 5)
expect(old).to_equal(42)
expect(csr.read(CSR_MSCRATCH)).to_equal(5)
```

</details>

#### CSRRSI: sets bits from immediate

1. var csr =  create csr
2. csr write
   - Expected: old equals `0x0F`
   - Expected: csr.read(CSR_MIE) equals `0x1F`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MIE, 0x0F)
val old = csr.csrrs(CSR_MIE, 0x10)
expect(old).to_equal(0x0F)
expect(csr.read(CSR_MIE)).to_equal(0x1F)
```

</details>

#### CSRRCI: clears bits from immediate

1. var csr =  create csr
2. csr write
   - Expected: old equals `0xFF`
   - Expected: csr.read(CSR_MIE) equals `0xF0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _create_csr()
csr.write(CSR_MIE, 0xFF)
val old = csr.csrrc(CSR_MIE, 0x0F)
expect(old).to_equal(0xFF)
expect(csr.read(CSR_MIE)).to_equal(0xF0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
