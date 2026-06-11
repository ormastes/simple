# Mir Builder Intensive Specification

> 1. builder add const int

<!-- sdn-diagram:id=mir_builder_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_builder_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_builder_intensive_spec -> std
mir_builder_intensive_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_builder_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Builder Intensive Specification

## Scenarios

### Mir Builder Intensive

#### emits mixed builder instructions in order

1. builder add const int

2. builder add const float

3. builder add const bool

4. builder add add

5. builder add mul

6. builder add branch

7. builder add ret
   - Expected: tc.instructions.len() equals `7`
   - Expected: tc.instructions[0] equals `MirTestInst.ConstInt(VReg(id: 0), 0)`
   - Expected: tc.instructions[1] equals `MirTestInst.ConstFloat(VReg(id: 1), 3.5)`
   - Expected: tc.instructions[2] equals `MirTestInst.ConstBool(VReg(id: 2), true)`
   - Expected: tc.instructions[3] equals `MirTestInst.Add(VReg(id: 3), VReg(id: 0), VReg(id: 0))`
   - Expected: tc.instructions[4] equals `MirTestInst.Mul(VReg(id: 4), VReg(id: 3), VReg(id: 0))`
   - Expected: tc.instructions[5] equals `MirTestInst.Branch(VReg(id: 2), BlockId(id: 10), BlockId(id: 20))`
   - Expected: tc.instructions[6] equals `MirTestInst.Ret(VReg(id: 4))`


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder("intensive")
builder.add_const_int(0, 0)
builder.add_const_float(1, 3.5)
builder.add_const_bool(2, true)
builder.add_add(3, 0, 0)
builder.add_mul(4, 3, 0)
builder.add_branch(2, 10, 20)
builder.add_ret(4)

val tc = builder.build()

expect(tc.instructions.len()).to_equal(7)
expect(tc.instructions[0]).to_equal(MirTestInst.ConstInt(VReg(id: 0), 0))
expect(tc.instructions[1]).to_equal(MirTestInst.ConstFloat(VReg(id: 1), 3.5))
expect(tc.instructions[2]).to_equal(MirTestInst.ConstBool(VReg(id: 2), true))
expect(tc.instructions[3]).to_equal(MirTestInst.Add(VReg(id: 3), VReg(id: 0), VReg(id: 0)))
expect(tc.instructions[4]).to_equal(MirTestInst.Mul(VReg(id: 4), VReg(id: 3), VReg(id: 0)))
expect(tc.instructions[5]).to_equal(MirTestInst.Branch(VReg(id: 2), BlockId(id: 10), BlockId(id: 20)))
expect(tc.instructions[6]).to_equal(MirTestInst.Ret(VReg(id: 4)))
```

</details>

#### tracks sparse virtual register usage

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

#### preserves backend selection overrides

1. builder only backend
   - Expected: tc.expected_backends.len() equals `1`
   - Expected: tc.expected_backends[0] equals `BackendTarget.Interpreter`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder("backends")
builder.only_backend(BackendTarget.Interpreter)

val tc = builder.build()

expect(tc.expected_backends.len()).to_equal(1)
expect(tc.expected_backends[0]).to_equal(BackendTarget.Interpreter)
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
| Source | `test/01_unit/compiler/backend/mir_builder_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mir Builder Intensive

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
