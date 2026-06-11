# rv64_mem_stage_spec

> RV64 Memory Stage Unit Specification

<!-- sdn-diagram:id=rv64_mem_stage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_mem_stage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_mem_stage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_mem_stage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_mem_stage_spec

RV64 Memory Stage Unit Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HW-RV64-PIPE-MEM |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/hardware/rv64/pipeline/rv64_mem_stage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

RV64 Memory Stage Unit Specification

Tests load and store operations: byte, halfword, word, doubleword,
sign-extension, and zero-extension.

## Scenarios

### Memory sign extension helpers

#### sign-extends positive byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_ext_byte(0x7F)).to_equal(127)
```

</details>

#### sign-extends negative byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_ext_byte(0x80)).to_equal(-128)
```

</details>

#### sign-extends positive halfword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_ext_half(0x7FFF)).to_equal(32767)
```

</details>

#### sign-extends negative halfword

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_ext_half(0x8000)).to_equal(-32768)
```

</details>

#### sign-extends positive word

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_ext_word(0x7FFFFFFF)).to_equal(2147483647)
```

</details>

#### sign-extends negative word

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sign_ext_word(0x80000000)).to_equal(-2147483648)
```

</details>

### Rv64Memory.load_funct3

#### loads byte with sign extension (LB, funct3=0)

1. var mem = create rv64 memory
2. mem write byte
   - Expected: mem.load_funct3(10, 0) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.write_byte(10, 0xFF)
expect(mem.load_funct3(10, 0)).to_equal(-1)
```

</details>

#### loads byte zero-extended (LBU, funct3=4)

1. var mem = create rv64 memory
2. mem write byte
   - Expected: mem.load_funct3(10, 4) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.write_byte(10, 0xFF)
expect(mem.load_funct3(10, 4)).to_equal(255)
```

</details>

#### loads word sign-extended (LW, funct3=2)

1. var mem = create rv64 memory
2. mem write word32
   - Expected: mem.load_funct3(0, 2) equals `-2147483647`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.write_word32(0, 0x80000001)
expect(mem.load_funct3(0, 2)).to_equal(-2147483647)
```

</details>

#### loads word zero-extended (LWU, funct3=6)

1. var mem = create rv64 memory
2. mem write word32
   - Expected: mem.load_funct3(0, 6) equals `0x80000001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.write_word32(0, 0x80000001)
expect(mem.load_funct3(0, 6)).to_equal(0x80000001)
```

</details>

#### loads doubleword (LD, funct3=3)

1. var mem = create rv64 memory
2. mem write word64
   - Expected: mem.load_funct3(0, 3) equals `0x0102030405060708`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.write_word64(0, 0x0102030405060708)
expect(mem.load_funct3(0, 3)).to_equal(0x0102030405060708)
```

</details>

### Rv64Memory.store_funct3

#### stores byte (SB, funct3=0)

1. var mem = create rv64 memory
2. mem store funct3
   - Expected: mem.read_byte(10) equals `0xCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.store_funct3(10, 0xABCD, 0)
expect(mem.read_byte(10)).to_equal(0xCD)
```

</details>

#### stores halfword (SH, funct3=1)

1. var mem = create rv64 memory
2. mem store funct3
   - Expected: mem.read_byte(10) equals `0x34`
   - Expected: mem.read_byte(11) equals `0x12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.store_funct3(10, 0x1234, 1)
expect(mem.read_byte(10)).to_equal(0x34)
expect(mem.read_byte(11)).to_equal(0x12)
```

</details>

#### stores word (SW, funct3=2)

1. var mem = create rv64 memory
2. mem store funct3
   - Expected: mem.read_word32(0) equals `0xDEADBEEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.store_funct3(0, 0xDEADBEEF, 2)
expect(mem.read_word32(0)).to_equal(0xDEADBEEF)
```

</details>

#### stores doubleword (SD, funct3=3)

1. var mem = create rv64 memory
2. mem store funct3
   - Expected: mem.read_word64(0) equals `0x0102030405060708`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(256)
mem.store_funct3(0, 0x0102030405060708, 3)
expect(mem.read_word64(0)).to_equal(0x0102030405060708)
```

</details>

### Rv64MemStage

#### produces invalid latch for invalid input

1. var ms = create rv64 mem stage
2. var mem = create rv64 memory
   - Expected: latch.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ms = create_rv64_mem_stage()
var mem = create_rv64_memory(256)
val latch = ms.tick(create_ex_mem_latch(), mem)
expect(latch.valid).to_equal(false)
```

</details>

#### passes ALU result through for non-memory instruction

1. var ms = create rv64 mem stage
2. var mem = create rv64 memory
   - Expected: latch.valid is true
   - Expected: latch.alu_result equals `42`
   - Expected: latch.mem_to_reg is false
   - Expected: latch.reg_write is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ms = create_rv64_mem_stage()
var mem = create_rv64_memory(256)
val ex_mem = Rv64ExMemLatch(
    pc: 0, alu_result: 42, rs2_val: 0, rd: 5,
    mem_read: false, mem_write: false, mem_to_reg: false,
    reg_write: true, branch_taken: false, branch_target: 0,
    funct3: 0, valid: true
)
val latch = ms.tick(ex_mem, mem)
expect(latch.valid).to_equal(true)
expect(latch.alu_result).to_equal(42)
expect(latch.mem_to_reg).to_equal(false)
expect(latch.reg_write).to_equal(true)
```

</details>

#### loads a word from memory on mem_read

1. var ms = create rv64 mem stage
2. var mem = create rv64 memory
3. mem write word32
   - Expected: latch.mem_data equals `0x12345678`
   - Expected: latch.mem_to_reg is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ms = create_rv64_mem_stage()
var mem = create_rv64_memory(256)
mem.write_word32(100, 0x12345678)
val ex_mem = Rv64ExMemLatch(
    pc: 0, alu_result: 100, rs2_val: 0, rd: 3,
    mem_read: true, mem_write: false, mem_to_reg: true,
    reg_write: true, branch_taken: false, branch_target: 0,
    funct3: 2, valid: true
)
val latch = ms.tick(ex_mem, mem)
expect(latch.mem_data).to_equal(0x12345678)
expect(latch.mem_to_reg).to_equal(true)
```

</details>

#### stores a word to memory via tick_store

1. var ms = create rv64 mem stage
2. var mem = create rv64 memory
3. ms tick store
   - Expected: mem.read_word32(200) equals `0xCAFE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ms = create_rv64_mem_stage()
var mem = create_rv64_memory(256)
val ex_mem = Rv64ExMemLatch(
    pc: 0, alu_result: 200, rs2_val: 0xCAFE, rd: 0,
    mem_read: false, mem_write: true, mem_to_reg: false,
    reg_write: false, branch_taken: false, branch_target: 0,
    funct3: 2, valid: true
)
ms.tick_store(ex_mem, mem)
expect(mem.read_word32(200)).to_equal(0xCAFE)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
