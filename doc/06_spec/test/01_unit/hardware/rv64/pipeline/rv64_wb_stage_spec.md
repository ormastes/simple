# rv64_wb_stage_spec

> RV64 Writeback Stage Unit Specification

<!-- sdn-diagram:id=rv64_wb_stage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_wb_stage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_wb_stage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_wb_stage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_wb_stage_spec

RV64 Writeback Stage Unit Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HW-RV64-PIPE-WB |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/hardware/rv64/pipeline/rv64_wb_stage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

RV64 Writeback Stage Unit Specification

Tests register writeback for ALU results and memory loads, including
x0 write suppression.

## Scenarios

### Rv64WbStage

#### does nothing for invalid latch

1. var wb = create rv64 wb stage
2. var rf = create rv64 register file
3. wb tick
   - Expected: rf.read(1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wb = create_rv64_wb_stage()
var rf = create_rv64_register_file()
wb.tick(create_mem_wb_latch(), rf)
expect(rf.read(1)).to_equal(0)
```

</details>

#### does nothing when reg_write is false

1. var wb = create rv64 wb stage
2. var rf = create rv64 register file
3. wb tick
   - Expected: rf.read(5) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wb = create_rv64_wb_stage()
var rf = create_rv64_register_file()
val latch = Rv64MemWbLatch(
    alu_result: 99, mem_data: 0, rd: 5,
    mem_to_reg: false, reg_write: false, valid: true
)
wb.tick(latch, rf)
expect(rf.read(5)).to_equal(0)
```

</details>

#### writes ALU result to rd when reg_write and not mem_to_reg

1. var wb = create rv64 wb stage
2. var rf = create rv64 register file
3. wb tick
   - Expected: rf.read(7) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wb = create_rv64_wb_stage()
var rf = create_rv64_register_file()
val latch = Rv64MemWbLatch(
    alu_result: 42, mem_data: 0, rd: 7,
    mem_to_reg: false, reg_write: true, valid: true
)
wb.tick(latch, rf)
expect(rf.read(7)).to_equal(42)
```

</details>

#### writes mem_data to rd when mem_to_reg is true

1. var wb = create rv64 wb stage
2. var rf = create rv64 register file
3. wb tick
   - Expected: rf.read(10) equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wb = create_rv64_wb_stage()
var rf = create_rv64_register_file()
val latch = Rv64MemWbLatch(
    alu_result: 999, mem_data: 0x12345678, rd: 10,
    mem_to_reg: true, reg_write: true, valid: true
)
wb.tick(latch, rf)
expect(rf.read(10)).to_equal(0x12345678)
```

</details>

#### does not write to x0 even with reg_write

1. var wb = create rv64 wb stage
2. var rf = create rv64 register file
3. wb tick
   - Expected: rf.read(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wb = create_rv64_wb_stage()
var rf = create_rv64_register_file()
val latch = Rv64MemWbLatch(
    alu_result: 42, mem_data: 0, rd: 0,
    mem_to_reg: false, reg_write: true, valid: true
)
wb.tick(latch, rf)
expect(rf.read(0)).to_equal(0)
```

</details>

#### select_wb_data returns ALU result when not mem_to_reg

1. var wb = create rv64 wb stage
   - Expected: wb.select_wb_data(latch) equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wb = create_rv64_wb_stage()
val latch = Rv64MemWbLatch(
    alu_result: 55, mem_data: 77, rd: 1,
    mem_to_reg: false, reg_write: true, valid: true
)
expect(wb.select_wb_data(latch)).to_equal(55)
```

</details>

#### select_wb_data returns mem_data when mem_to_reg

1. var wb = create rv64 wb stage
   - Expected: wb.select_wb_data(latch) equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wb = create_rv64_wb_stage()
val latch = Rv64MemWbLatch(
    alu_result: 55, mem_data: 77, rd: 1,
    mem_to_reg: true, reg_write: true, valid: true
)
expect(wb.select_wb_data(latch)).to_equal(77)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
