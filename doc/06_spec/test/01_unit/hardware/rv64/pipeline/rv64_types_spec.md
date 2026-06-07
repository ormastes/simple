# rv64_types_spec

> RV64 Pipeline Types Unit Specification

<!-- sdn-diagram:id=rv64_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_types_spec

RV64 Pipeline Types Unit Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HW-RV64-PIPE-TYPES |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/hardware/rv64/pipeline/rv64_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

RV64 Pipeline Types Unit Specification

Tests the register file, memory model, and latch constructors.

## Scenarios

### Rv64RegisterFile

#### initializes all 32 registers to zero

1. var rf = create rv64 register file
   - Expected: rf.read(0) equals `0`
   - Expected: rf.read(1) equals `0`
   - Expected: rf.read(31) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = create_rv64_register_file()
expect(rf.read(0)).to_equal(0)
expect(rf.read(1)).to_equal(0)
expect(rf.read(31)).to_equal(0)
```

</details>

#### x0 always reads as zero even after write

1. var rf = create rv64 register file
2. rf write
   - Expected: rf.read(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = create_rv64_register_file()
rf.write(0, 42)
expect(rf.read(0)).to_equal(0)
```

</details>

#### reads and writes general purpose registers

1. var rf = create rv64 register file
2. rf write
3. rf write
   - Expected: rf.read(1) equals `100`
   - Expected: rf.read(31) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = create_rv64_register_file()
rf.write(1, 100)
rf.write(31, -1)
expect(rf.read(1)).to_equal(100)
expect(rf.read(31)).to_equal(-1)
```

</details>

#### handles 64-bit values

1. var rf = create rv64 register file
2. rf write
   - Expected: rf.read(10) equals `large_val`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = create_rv64_register_file()
val large_val = 0x7FFFFFFFFFFFFFFF
rf.write(10, large_val)
expect(rf.read(10)).to_equal(large_val)
```

</details>

#### ignores out-of-range reads and writes

1. var rf = create rv64 register file
   - Expected: rf.read(32) equals `0`
   - Expected: rf.read(-1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rf = create_rv64_register_file()
expect(rf.read(32)).to_equal(0)
expect(rf.read(-1)).to_equal(0)
```

</details>

### Rv64Memory

#### initializes to zero

1. var mem = create rv64 memory
   - Expected: mem.read_byte(0) equals `0`
   - Expected: mem.read_byte(255) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
expect(mem.read_byte(0)).to_equal(0)
expect(mem.read_byte(255)).to_equal(0)
```

</details>

#### reads and writes individual bytes

1. var mem = create rv64 memory
2. mem write byte
   - Expected: mem.read_byte(10) equals `0xAB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.write_byte(10, 0xAB)
expect(mem.read_byte(10)).to_equal(0xAB)
```

</details>

#### reads and writes 32-bit words little-endian

1. var mem = create rv64 memory
2. mem write word32
   - Expected: mem.read_byte(0) equals `0x78`
   - Expected: mem.read_byte(1) equals `0x56`
   - Expected: mem.read_byte(2) equals `0x34`
   - Expected: mem.read_byte(3) equals `0x12`
   - Expected: mem.read_word32(0) equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.write_word32(0, 0x12345678)
expect(mem.read_byte(0)).to_equal(0x78)
expect(mem.read_byte(1)).to_equal(0x56)
expect(mem.read_byte(2)).to_equal(0x34)
expect(mem.read_byte(3)).to_equal(0x12)
expect(mem.read_word32(0)).to_equal(0x12345678)
```

</details>

#### reads and writes 64-bit words little-endian

1. var mem = create rv64 memory
2. mem write word64
   - Expected: mem.read_word64(0) equals `0x0102030405060708`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.write_word64(0, 0x0102030405060708)
expect(mem.read_word64(0)).to_equal(0x0102030405060708)
```

</details>

#### handles out-of-range access gracefully

1. var mem = create rv64 memory
   - Expected: mem.read_byte(100) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(16)
expect(mem.read_byte(100)).to_equal(0)
```

</details>

### Pipeline Latch Constructors

#### creates invalid IF/ID latch by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latch = create_if_id_latch()
expect(latch.valid).to_equal(false)
expect(latch.pc).to_equal(0)
```

</details>

#### creates invalid ID/EX latch by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latch = create_id_ex_latch()
expect(latch.valid).to_equal(false)
expect(latch.reg_write).to_equal(false)
```

</details>

#### creates invalid EX/MEM latch by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latch = create_ex_mem_latch()
expect(latch.valid).to_equal(false)
```

</details>

#### creates invalid MEM/WB latch by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latch = create_mem_wb_latch()
expect(latch.valid).to_equal(false)
```

</details>

### Rv64AluOp

#### converts to readable text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Rv64AluOp.Add.to_text()).to_equal("add")
expect(Rv64AluOp.Addw.to_text()).to_equal("addw")
expect(Rv64AluOp.PassB.to_text()).to_equal("passb")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
