# Backend Capability Specification

> Tests covering Backend Capability, Backend Capability Detection, Backend Selection Logic, Backend Fallback Behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Capability Specification

## Scenarios

### Backend Capability

#### names the backend and unsupported async operation in C lowering

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- names the backend and unsupported async operation in C lowering
   - Expected: output does not contain `not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the backend and unsupported async operation in C lowering")
val output = c_output_for(
    _1.translate_create_promise(
        LocalId(id: 1),
        LocalId(id: 2),
        MirType.promise(MirType.i64())
    )
)

expect(output).to_contain("C backend does not support async CreatePromise lowering")
expect(output.contains("not implemented")).to_equal(false)
```

</details>

#### names the backend and unsupported actor operation in C lowering

- names the backend and unsupported actor operation in C lowering
   - Expected: output does not contain `Instruction not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the backend and unsupported actor operation in C lowering")
val output = c_output_for(
    _1.translate_receive(LocalId(id: 1), nil)
)

expect(output).to_contain("C backend does not support actor Receive lowering")
expect(output.contains("Instruction not implemented")).to_equal(false)
```

</details>

<details>
<summary>Advanced: names the backend and unsupported matrix operation in LLVM lowering</summary>

#### names the backend and unsupported matrix operation in LLVM lowering

- names the backend and unsupported matrix operation in LLVM lowering
   - Expected: output does not contain `@__simple_runtime_matmul`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the backend and unsupported matrix operation in LLVM lowering")
val output = llvm_output_for(\translator:
    translator.local_types[0] = "ptr"
    translator.local_types[1] = "ptr"
    translator.local_types[2] = "ptr"
    translator.translate_binop(
        LocalId(id: 2),
        MirBinOp.MatMul,
        mir_operand_copy(LocalId(id: 0)),
        mir_operand_copy(LocalId(id: 1))
    )
)

expect(output).to_contain("LLVM backend does not support MatMul lowering")
expect(output.contains("@__simple_runtime_matmul")).to_equal(false)
```

</details>


</details>

#### lowers optimizer pseudo SSA phi to a native LLVM phi

- lowers optimizer pseudo SSA phi to a native LLVM phi
   - Expected: output does not contain `@__simple_intrinsic___simple_ssa_phi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers optimizer pseudo SSA phi to a native LLVM phi")
val output = llvm_output_for(\translator:
    translator.local_types[10] = "i64"
    translator.local_types[11] = "i64"
    translator.local_types[12] = "i64"
    translator.translate_intrinsic(
        Some(LocalId(id: 12)),
        "__simple_ssa_phi",
        [
            mir_operand_const_int(1),
            mir_operand_copy(LocalId(id: 10)),
            mir_operand_const_int(2),
            mir_operand_copy(LocalId(id: 11))
        ]
    )
)

expect(output).to_contain("%l12 = phi i64 [ %l10, %bb1 ], [ %l11, %bb2 ]")
expect(output.contains("@__simple_intrinsic___simple_ssa_phi")).to_equal(false)
```

</details>

#### keeps unsupported messages actionable instead of generic

- keeps unsupported messages actionable instead of generic
   - Expected: output does not contain `Instruction not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps unsupported messages actionable instead of generic")
val output = llvm_output_for(\translator:
    translator.local_types[0] = "ptr"
    translator.local_types[2] = "ptr"
    translator.translate_unaryop(
        LocalId(id: 2),
        MirUnaryOp.Transpose,
        mir_operand_copy(LocalId(id: 0))
    )
)

expect(output).to_contain("LLVM backend does not support Transpose lowering")
expect(output.contains("Instruction not implemented")).to_equal(false)
```

</details>

#### keeps the VHDL process helper module importable

- keeps the VHDL process helper module importable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the VHDL process helper module importable")
expect(vhdl_compile_match_u8()).to_contain("case opcode is")
expect(vhdl_compile_clocked_process()).to_contain("rising_edge(clk)")
```

</details>

### Backend Capability Detection

#### Cranelift backend capabilities

#### supports basic arithmetic

- supports basic arithmetic
   - Expected: test_case.is_supported(BackendTarget.Cranelift) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports basic arithmetic")
val builder = MirTestBuilder.new()
val v0 = builder.vreg(0)
val v1 = builder.vreg(1)
val v2 = builder.vreg(2)

builder.const_int(v0, 10)
builder.const_int(v1, 20)
builder.add(v2, v0, v1)
builder.ret(v2)

val test_case = builder.build()
# Cranelift should support basic arithmetic
expect(test_case.is_supported(BackendTarget.Cranelift)).to_equal(true)
```

</details>

#### does not claim SIMD support

- does not claim SIMD support
   - Expected: test_case.instruction_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not claim SIMD support")
# Cranelift doesn't support advanced SIMD
val builder = MirTestBuilder.new()
val vec_reg = builder.vreg(0)
val result = builder.vreg(1)

builder.vec_sum(result, vec_reg)
builder.ret(result)

val test_case = builder.build()
expect(test_case.instruction_count()).to_equal(2)
```

</details>

#### does not claim GPU support

- does not claim GPU support
   - Expected: test_case.instruction_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not claim GPU support")
val builder = MirTestBuilder.new()
val id = builder.vreg(0)

builder.gpu_global_id(id, 0)
builder.ret(id)

val test_case = builder.build()
# Cranelift doesn't support GPU instructions
expect(test_case.instruction_count()).to_equal(2)
```

</details>

#### LLVM backend capabilities

#### supports basic arithmetic

- supports basic arithmetic
   - Expected: test_case.is_supported(BackendTarget.LLVM) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports basic arithmetic")
val builder = MirTestBuilder.new()
val v0 = builder.vreg(0)
val v1 = builder.vreg(1)
val v2 = builder.vreg(2)

builder.const_int(v0, 5)
builder.const_int(v1, 7)
builder.mul(v2, v0, v1)
builder.ret(v2)

val test_case = builder.build()
expect(test_case.is_supported(BackendTarget.LLVM)).to_equal(true)
```

</details>

#### does not yet lower SIMD reduction

- does not yet lower SIMD reduction
   - Expected: test_case.is_supported(BackendTarget.LLVM) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not yet lower SIMD reduction")
# MTB1 2026-07-30: adapted from a fictional "supports SIMD
# operations" expectation. The real LLVM text backend
# (_MirToLlvm/aggregate_intrinsics.spl translate_simd_horizontal)
# unconditionally emits an unsupported-backend panic for SIMD
# reduction -- there is no implementation to claim support for.
val builder = MirTestBuilder.new()
val v0 = builder.vreg(0)
val v1 = builder.vreg(1)
val v2 = builder.vreg(2)
val v3 = builder.vreg(3)
val vec_val = builder.vreg(4)
val sum = builder.vreg(5)

builder.const_float(v0, 1.0)
builder.const_float(v1, 2.0)
builder.const_float(v2, 3.0)
builder.const_float(v3, 4.0)
builder.vec_lit(vec_val, [v0, v1, v2, v3])
builder.vec_sum(sum, vec_val)
builder.ret(sum)

val test_case = builder.build()
expect(test_case.is_supported(BackendTarget.LLVM)).to_equal(false)
```

</details>

#### Vulkan backend capabilities

#### supports GPU work item IDs

- supports GPU work item IDs
   - Expected: test_case.is_supported(BackendTarget.Vulkan) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports GPU work item IDs")
val builder = MirTestBuilder.new()
val id = builder.vreg(0)

builder.gpu_global_id(id, 0)
builder.ret(id)

val test_case = builder.build()
expect(test_case.is_supported(BackendTarget.Vulkan)).to_equal(true)
```

</details>

#### supports GPU barriers

- supports GPU barriers
   - Expected: test_case.is_supported(BackendTarget.Vulkan) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports GPU barriers")
val builder = MirTestBuilder.new()

builder.gpu_barrier()
builder.ret_void()

val test_case = builder.build()
expect(test_case.is_supported(BackendTarget.Vulkan)).to_equal(true)
```

</details>

#### supports GPU atomics

- supports GPU atomics
   - Expected: test_case.is_supported(BackendTarget.Vulkan) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports GPU atomics")
val builder = MirTestBuilder.new()
val ptr = builder.vreg(0)
val value = builder.vreg(1)
val old = builder.vreg(2)

builder.const_int(value, 1)
builder.gpu_atomic_add(old, ptr, value)
builder.ret(old)

val test_case = builder.build()
expect(test_case.is_supported(BackendTarget.Vulkan)).to_equal(true)
```

</details>

#### Interpreter backend capabilities

#### supports all instruction types

- supports all instruction types
   - Expected: test_case.is_supported(BackendTarget.Interpreter) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports all instruction types")
# Interpreter should support everything as fallback
val builder = MirTestBuilder.new()

val v0 = builder.vreg(0)
builder.const_int(v0, 42)

val actor_reg = builder.vreg(1)
val body = builder.block(0)
builder.actor_spawn(actor_reg, body)

builder.ret_void()

val test_case = builder.build()
expect(test_case.is_supported(BackendTarget.Interpreter)).to_equal(true)
```

</details>

### Backend Selection Logic

#### pure arithmetic code

#### selects any compiled backend

- selects any compiled backend
   - Expected: test_case.is_supported(BackendTarget.Cranelift) is true
   - Expected: test_case.is_supported(BackendTarget.LLVM) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects any compiled backend")
val builder = MirTestBuilder.new()
val v0 = builder.vreg(0)
val v1 = builder.vreg(1)
val v2 = builder.vreg(2)

builder.const_int(v0, 10)
builder.const_int(v1, 20)
builder.add(v2, v0, v1)
builder.ret(v2)

val test_case = builder.build()
# Should work on Cranelift or LLVM
expect(test_case.is_supported(BackendTarget.Cranelift)).to_equal(true)
expect(test_case.is_supported(BackendTarget.LLVM)).to_equal(true)
```

</details>

#### SIMD-heavy code

#### does not yet route to LLVM for SIMD reduction

- does not yet route to LLVM for SIMD reduction
   - Expected: test_case.is_supported(BackendTarget.LLVM) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not yet route to LLVM for SIMD reduction")
# MTB1 2026-07-30: adapted from a fictional "prefers LLVM
# backend" expectation -- same real finding as "does not yet
# lower SIMD reduction" above: the LLVM text backend has no
# working SIMD-reduction lowering to prefer. Also fixes the
# scaffold's undeclared `vec` reference (only `vec_val` existed).
val builder = MirTestBuilder.new()
val vec_val = builder.vreg(0)
val sum = builder.vreg(1)

builder.vec_sum(sum, vec_val)
builder.ret(sum)

val test_case = builder.build()
expect(test_case.is_supported(BackendTarget.LLVM)).to_equal(false)
```

</details>

#### GPU kernel code

#### requires Vulkan backend

- requires Vulkan backend
   - Expected: test_case.is_supported(BackendTarget.Vulkan) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires Vulkan backend")
val builder = MirTestBuilder.new()
val id = builder.vreg(0)

builder.gpu_global_id(id, 0)
builder.ret(id)

val test_case = builder.build()
# GPU requires Vulkan
expect(test_case.is_supported(BackendTarget.Vulkan)).to_equal(true)
```

</details>

#### actor-based code

#### requires interpreter

- requires interpreter
   - Expected: test_case.is_supported(BackendTarget.Interpreter) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires interpreter")
val builder = MirTestBuilder.new()
val actor_reg = builder.vreg(0)
val body = builder.block(0)

builder.actor_spawn(actor_reg, body)
builder.ret_void()

val test_case = builder.build()
# Actors only in interpreter
expect(test_case.is_supported(BackendTarget.Interpreter)).to_equal(true)
```

</details>

### Backend Fallback Behavior

#### mixed instruction types

#### falls back for unsupported features

- falls back for unsupported features
   - Expected: test_case.is_supported(BackendTarget.Interpreter) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back for unsupported features")
# Code mixing compiled and interpreted features
val builder = MirTestBuilder.new()

# Arithmetic (supported)
val v0 = builder.vreg(0)
builder.const_int(v0, 42)

# Actor (not supported in compiled)
val actor_reg = builder.vreg(1)
val body = builder.block(0)
builder.actor_spawn(actor_reg, body)

builder.ret_void()

val test_case = builder.build()
# Should only work in interpreter
expect(test_case.is_supported(BackendTarget.Interpreter)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/backend_capability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Backend Capability, Backend Capability Detection, Backend Selection Logic, Backend Fallback Behavior.
- Backend Capability
- Backend Capability Detection
- Backend Selection Logic
- Backend Fallback Behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7a500b655dfbd6097c4df0253fc38ac70bf737e0d12e15acd597ec84eb9818ef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a500b655dfbd6097c4df0253fc38ac70bf737e0d12e15acd597ec84eb9818ef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a500b655dfbd6097c4df0253fc38ac70bf737e0d12e15acd597ec84eb9818ef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/backend/backend_capability_spec.spl
mirror: doc/06_spec/unit/compiler/backend/backend_capability_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/backend_capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/backend_capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/backend_capability_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/backend_capability_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the backend and unsupported async operation in C lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/backend_capability_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the backend and unsupported actor operation in C lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/backend_capability_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the backend and unsupported matrix operation in LLVM lowering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
