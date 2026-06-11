# RV32 CSR Unit Tests

> Unit tests for Control and Status Register file operations.

<!-- sdn-diagram:id=rv32_csr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv32_csr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv32_csr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv32_csr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV32 CSR Unit Tests

Unit tests for Control and Status Register file operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV32-CSR-001 |
| Category | Hardware |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/01_unit/hardware/rv32imac/rv32_csr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for Control and Status Register file operations.

## Scenarios

### CSR Read/Write

#### writes and reads mtvec

1. var csr =  new csr
2. csr write
   - Expected: csr.read(CSR_MTVEC) equals `0x80000100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MTVEC, 0x80000100)
expect(csr.read(CSR_MTVEC)).to_equal(0x80000100)
```

</details>

#### writes and reads mscratch

1. var csr =  new csr
2. csr write
   - Expected: csr.read(CSR_MSCRATCH) equals `0xCAFEBABE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MSCRATCH, 0xCAFEBABE)
expect(csr.read(CSR_MSCRATCH)).to_equal(0xCAFEBABE)
```

</details>

#### mepc is word-aligned

1. var csr =  new csr
2. csr write
   - Expected: csr.read(CSR_MEPC) equals `0x80001000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MEPC, 0x80001003)
expect(csr.read(CSR_MEPC)).to_equal(0x80001000)
```

</details>

#### misa reports RV32IMAC

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val csr = _new_csr()
expect(csr.read(CSR_MISA)).to_equal(0x40101104)
```

</details>

### CSR Atomic Operations

#### CSRRW swaps value

1. var csr =  new csr
2. csr write
   - Expected: old equals `0xAAAAAAAA`
   - Expected: csr.read(CSR_MSCRATCH) equals `0x55555555`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MSCRATCH, 0xAAAAAAAA)
val old = csr.csrrw(CSR_MSCRATCH, 0x55555555)
expect(old).to_equal(0xAAAAAAAA)
expect(csr.read(CSR_MSCRATCH)).to_equal(0x55555555)
```

</details>

#### CSRRS sets bits

1. var csr =  new csr
2. csr write
3. csr csrrs
   - Expected: csr.read(CSR_MIE) equals `0x88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MIE, 0x00)
csr.csrrs(CSR_MIE, 0x88)
expect(csr.read(CSR_MIE)).to_equal(0x88)
```

</details>

#### CSRRS with rs1=0 is read-only

1. var csr =  new csr
2. csr write
   - Expected: old equals `0xFF`
   - Expected: csr.read(CSR_MIE) equals `0xFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MIE, 0xFF)
val old = csr.csrrs(CSR_MIE, 0)
expect(old).to_equal(0xFF)
expect(csr.read(CSR_MIE)).to_equal(0xFF)
```

</details>

#### CSRRC clears bits

1. var csr =  new csr
2. csr write
3. csr csrrc
   - Expected: csr.read(CSR_MIE) equals `0xF0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MIE, 0xFF)
csr.csrrc(CSR_MIE, 0x0F)
expect(csr.read(CSR_MIE)).to_equal(0xF0)
```

</details>

### CSR Trap Handling

#### saves state on trap entry

1. var csr =  new csr
2. csr write
3. csr write
4. csr trap enter
   - Expected: csr.read(CSR_MEPC) equals `0x80001234`
   - Expected: csr.read(CSR_MCAUSE) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MTVEC, 0x80000100)
csr.write(CSR_MSTATUS, 0x08)  # MIE=1
csr.trap_enter(11, 0x80001234, 0)
expect(csr.read(CSR_MEPC)).to_equal(0x80001234)
expect(csr.read(CSR_MCAUSE)).to_equal(11)
```

</details>

#### trap_vector returns aligned mtvec

1. var csr =  new csr
2. csr write
   - Expected: csr.trap_vector() equals `0x80000100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MTVEC, 0x80000103)  # mode bits in low 2
expect(csr.trap_vector()).to_equal(0x80000100)
```

</details>

#### mret returns to mepc

1. var csr =  new csr
2. csr write
3. csr trap enter
   - Expected: return_pc equals `0x80002000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.write(CSR_MTVEC, 0x80000100)
csr.trap_enter(11, 0x80002000, 0)
val return_pc = csr.trap_return()
expect(return_pc).to_equal(0x80002000)
```

</details>

#### tick increments mcycle

1. var csr =  new csr
2. csr tick
3. csr tick
4. csr tick
   - Expected: csr.read(CSR_MCYCLE) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.tick()
csr.tick()
csr.tick()
expect(csr.read(CSR_MCYCLE)).to_equal(3)
```

</details>

#### retire increments minstret

1. var csr =  new csr
2. csr retire
3. csr retire
   - Expected: csr.read(CSR_MINSTRET) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var csr = _new_csr()
csr.retire()
csr.retire()
expect(csr.read(CSR_MINSTRET)).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
