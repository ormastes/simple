# Mir Instruction Complete Specification

> 1. builder add const int

<!-- sdn-diagram:id=mir_instruction_complete_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_instruction_complete_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_instruction_complete_spec -> std
mir_instruction_complete_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_instruction_complete_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Instruction Complete Specification

## Scenarios

### Mir Instruction Complete

#### emits core builder instructions in order

1. builder add const int

2. builder add const bool

3. builder add add

4. builder add branch

5. builder add ret
   - Expected: tc.instructions.len() equals `5`
   - Expected: tc.instructions[0] equals `MirTestInst.ConstInt(VReg(id: 0), 10)`
   - Expected: tc.instructions[1] equals `MirTestInst.ConstBool(VReg(id: 1), true)`
   - Expected: tc.instructions[2] equals `MirTestInst.Add(VReg(id: 2), VReg(id: 0), VReg(id: 0))`
   - Expected: tc.instructions[4] equals `MirTestInst.Ret(VReg(id: 2))`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder("core")
builder.add_const_int(0, 10)
builder.add_const_bool(1, true)
builder.add_add(2, 0, 0)
builder.add_branch(1, 3, 4)
builder.add_ret(2)

val tc = builder.build()

expect(tc.instructions.len()).to_equal(5)
expect(tc.instructions[0]).to_equal(MirTestInst.ConstInt(VReg(id: 0), 10))
expect(tc.instructions[1]).to_equal(MirTestInst.ConstBool(VReg(id: 1), true))
expect(tc.instructions[2]).to_equal(MirTestInst.Add(VReg(id: 2), VReg(id: 0), VReg(id: 0)))
expect(tc.instructions[4]).to_equal(MirTestInst.Ret(VReg(id: 2)))
```

</details>

#### tracks the next virtual register from sparse destinations

1. builder add const int
   - Expected: builder.next_vreg equals `6`

2. builder add gpu global id
   - Expected: builder.next_vreg equals `6`

3. builder add mul
   - Expected: builder.next_vreg equals `21`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder("vregs")

expect(builder.next_vreg).to_equal(0)
builder.add_const_int(5, 100)
expect(builder.next_vreg).to_equal(6)
builder.add_gpu_global_id(2, 0)
expect(builder.next_vreg).to_equal(6)
builder.add_mul(20, 5, 2)
expect(builder.next_vreg).to_equal(21)
```

</details>

#### supports explicit backend restrictions

1. builder only backends
   - Expected: tc.expected_backends.len() equals `2`
   - Expected: tc.expected_backends[0] equals `BackendTarget.LLVM`
   - Expected: tc.expected_backends[1] equals `BackendTarget.Interpreter`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder("backends")
builder.only_backends([BackendTarget.LLVM, BackendTarget.Interpreter])

val tc = builder.build()

expect(tc.expected_backends.len()).to_equal(2)
expect(tc.expected_backends[0]).to_equal(BackendTarget.LLVM)
expect(tc.expected_backends[1]).to_equal(BackendTarget.Interpreter)
```

</details>

#### keeps helper patterns deterministic

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arithmetic = simple_arithmetic()
val simd = simd_reduction()
val gpu_case = gpu_kernel()

expect(arithmetic.name).to_equal("simple_arithmetic")
expect(arithmetic.instructions.len()).to_equal(4)
expect(simd.expected_backends).to_equal([BackendTarget.LLVM, BackendTarget.Interpreter])
expect(gpu_case.expected_backends).to_equal([BackendTarget.Vulkan])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/mir_instruction_complete_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mir Instruction Complete

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
