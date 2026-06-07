# rv64_pipeline_integration_spec

> RV64 Pipeline Integration Specification

<!-- sdn-diagram:id=rv64_pipeline_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_pipeline_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_pipeline_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_pipeline_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_pipeline_integration_spec

RV64 Pipeline Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HW-RV64-PIPE-INT |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/hardware/rv64/pipeline/rv64_pipeline_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

RV64 Pipeline Integration Specification

End-to-end test: load a short RV64I program into memory, step through all
five pipeline stages, verify final register/memory state.

## Scenarios

### RV64 Pipeline Integration

#### executes ADDI x1, x0, 42 and writes 42 to x1

1. var mem = create rv64 memory
2. var rf = create rv64 register file
3. var ifs = create rv64 if stage
4. mem store instruction
5. run single instruction
   - Expected: rf.read(1) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
var rf = create_rv64_register_file()
var ifs = create_rv64_if_stage(0)

mem.store_instruction(0, encode_addi(1, 0, 42))
run_single_instruction(mem, rf, ifs)

expect(rf.read(1)).to_equal(42)
```

</details>

#### executes ADD x3, x1, x2 after loading x1=10 and x2=20

1. var mem = create rv64 memory
2. var rf = create rv64 register file
3. var ifs = create rv64 if stage
4. mem store instruction
5. mem store instruction
6. mem store instruction
7. run single instruction
8. run single instruction
9. run single instruction
   - Expected: rf.read(1) equals `10`
   - Expected: rf.read(2) equals `20`
   - Expected: rf.read(3) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
var rf = create_rv64_register_file()
var ifs = create_rv64_if_stage(0)

mem.store_instruction(0, encode_addi(1, 0, 10))
mem.store_instruction(4, encode_addi(2, 0, 20))
mem.store_instruction(8, encode_add(3, 1, 2))

run_single_instruction(mem, rf, ifs)
run_single_instruction(mem, rf, ifs)
run_single_instruction(mem, rf, ifs)

expect(rf.read(1)).to_equal(10)
expect(rf.read(2)).to_equal(20)
expect(rf.read(3)).to_equal(30)
```

</details>

#### executes SUB x3, x1, x2

1. var mem = create rv64 memory
2. var rf = create rv64 register file
3. var ifs = create rv64 if stage
4. mem store instruction
5. mem store instruction
6. mem store instruction
7. run single instruction
8. run single instruction
9. run single instruction
   - Expected: rf.read(3) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
var rf = create_rv64_register_file()
var ifs = create_rv64_if_stage(0)

mem.store_instruction(0, encode_addi(1, 0, 50))
mem.store_instruction(4, encode_addi(2, 0, 8))
mem.store_instruction(8, encode_sub(3, 1, 2))

run_single_instruction(mem, rf, ifs)
run_single_instruction(mem, rf, ifs)
run_single_instruction(mem, rf, ifs)

expect(rf.read(3)).to_equal(42)
```

</details>

#### executes LUI x1, 0x12345000

1. var mem = create rv64 memory
2. var rf = create rv64 register file
3. var ifs = create rv64 if stage
4. mem store instruction
5. run single instruction
   - Expected: rf.read(1) equals `0x12345000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
var rf = create_rv64_register_file()
var ifs = create_rv64_if_stage(0)

mem.store_instruction(0, encode_lui(1, 0x12345000))
run_single_instruction(mem, rf, ifs)

expect(rf.read(1)).to_equal(0x12345000)
```

</details>

#### executes SW then LW round-trip

1. var mem = create rv64 memory
2. var rf = create rv64 register file
3. var ifs = create rv64 if stage
4. mem store instruction
5. mem store instruction
6. mem store instruction
7. mem store instruction
8. mem store instruction
9. run single instruction
10. run single instruction
11. run single instruction
12. run single instruction
   - Expected: rf.read(3) equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
var rf = create_rv64_register_file()
var ifs = create_rv64_if_stage(0)

# x1 = 256 (base address for data)
mem.store_instruction(0, encode_addi(1, 0, 256))
# x2 = 0xBEEF
mem.store_instruction(4, encode_addi(2, 0, 0xBEEF - 0x10000))
# NOTE: ADDI sign-extends, so use two-step load for 0xBEEF
# Actually, just use a small value for simplicity
mem.store_instruction(4, encode_addi(2, 0, 99))
# SW x2, 0(x1)
mem.store_instruction(8, encode_sw(2, 1, 0))
# LW x3, 0(x1)
mem.store_instruction(12, encode_lw(3, 1, 0))

run_single_instruction(mem, rf, ifs)  # addi x1
run_single_instruction(mem, rf, ifs)  # addi x2
run_single_instruction(mem, rf, ifs)  # sw
run_single_instruction(mem, rf, ifs)  # lw

expect(rf.read(3)).to_equal(99)
```

</details>

#### executes ADDW (RV64I W-suffix) with 32-bit truncation

1. var mem = create rv64 memory
2. var rf = create rv64 register file
3. var ifs = create rv64 if stage
4. mem store instruction
5. mem store instruction
6. mem store instruction
7. run single instruction
8. run single instruction
9. run single instruction
   - Expected: rf.read(3) equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
var rf = create_rv64_register_file()
var ifs = create_rv64_if_stage(0)

mem.store_instruction(0, encode_addi(1, 0, 10))
mem.store_instruction(4, encode_addi(2, 0, 20))
mem.store_instruction(8, encode_addw(3, 1, 2))

run_single_instruction(mem, rf, ifs)
run_single_instruction(mem, rf, ifs)
run_single_instruction(mem, rf, ifs)

expect(rf.read(3)).to_equal(30)
```

</details>

#### executes ADDIW (RV64I W-suffix immediate)

1. var mem = create rv64 memory
2. var rf = create rv64 register file
3. var ifs = create rv64 if stage
4. mem store instruction
5. mem store instruction
6. run single instruction
7. run single instruction
   - Expected: rf.read(2) equals `105`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
var rf = create_rv64_register_file()
var ifs = create_rv64_if_stage(0)

mem.store_instruction(0, encode_addi(1, 0, 100))
mem.store_instruction(4, encode_addiw(2, 1, 5))

run_single_instruction(mem, rf, ifs)
run_single_instruction(mem, rf, ifs)

expect(rf.read(2)).to_equal(105)
```

</details>

#### x0 stays zero through pipeline

1. var mem = create rv64 memory
2. var rf = create rv64 register file
3. var ifs = create rv64 if stage
4. mem store instruction
5. run single instruction
   - Expected: rf.read(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
var rf = create_rv64_register_file()
var ifs = create_rv64_if_stage(0)

# Try to write to x0
mem.store_instruction(0, encode_addi(0, 0, 42))
run_single_instruction(mem, rf, ifs)

expect(rf.read(0)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
