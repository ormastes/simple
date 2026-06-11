# rv64_if_stage_spec

> RV64 Instruction Fetch Stage Unit Specification

<!-- sdn-diagram:id=rv64_if_stage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_if_stage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_if_stage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_if_stage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_if_stage_spec

RV64 Instruction Fetch Stage Unit Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HW-RV64-PIPE-IF |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/hardware/rv64/pipeline/rv64_if_stage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

RV64 Instruction Fetch Stage Unit Specification

Tests IF stage: PC management, instruction fetching, and branch override.

## Scenarios

### Rv64IfStage

#### starts at the configured PC

1. var ifs = create rv64 if stage
   - Expected: ifs.get_pc() equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ifs = create_rv64_if_stage(0x80000000)
expect(ifs.get_pc()).to_equal(0x80000000)
```

</details>

#### fetches an instruction and advances PC by 4

1. var mem = create rv64 memory
2. mem store instruction
3. var ifs = create rv64 if stage
   - Expected: latch.valid is true
   - Expected: latch.pc equals `0`
   - Expected: latch.instruction equals `inst`
   - Expected: ifs.get_pc() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
val inst = encode_addi(1, 0, 42)
mem.store_instruction(0, inst)
var ifs = create_rv64_if_stage(0)
val latch = ifs.tick(mem, false, 0)
expect(latch.valid).to_equal(true)
expect(latch.pc).to_equal(0)
expect(latch.instruction).to_equal(inst)
expect(ifs.get_pc()).to_equal(4)
```

</details>

#### fetches sequential instructions

1. var mem = create rv64 memory
2. mem store instruction
3. mem store instruction
4. var ifs = create rv64 if stage
   - Expected: l0.instruction equals `inst0`
   - Expected: l1.instruction equals `inst1`
   - Expected: ifs.get_pc() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
val inst0 = encode_addi(1, 0, 10)
val inst1 = encode_addi(2, 0, 20)
mem.store_instruction(0, inst0)
mem.store_instruction(4, inst1)
var ifs = create_rv64_if_stage(0)
val l0 = ifs.tick(mem, false, 0)
val l1 = ifs.tick(mem, false, 0)
expect(l0.instruction).to_equal(inst0)
expect(l1.instruction).to_equal(inst1)
expect(ifs.get_pc()).to_equal(8)
```

</details>

#### overrides PC on branch taken

1. var mem = create rv64 memory
2. mem store instruction
3. var ifs = create rv64 if stage
   - Expected: latch.pc equals `100`
   - Expected: latch.instruction equals `inst_at_100`
   - Expected: ifs.get_pc() equals `104`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem = create_rv64_memory(1024)
val inst_at_100 = encode_addi(5, 0, 99)
mem.store_instruction(100, inst_at_100)
var ifs = create_rv64_if_stage(0)
val latch = ifs.tick(mem, true, 100)
expect(latch.pc).to_equal(100)
expect(latch.instruction).to_equal(inst_at_100)
expect(ifs.get_pc()).to_equal(104)
```

</details>

#### supports manual PC override via set_pc

1. var ifs = create rv64 if stage
2. ifs set pc
   - Expected: ifs.get_pc() equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ifs = create_rv64_if_stage(0)
ifs.set_pc(0x1000)
expect(ifs.get_pc()).to_equal(0x1000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
