# Backend Capability Specification

> <details>

<!-- sdn-diagram:id=backend_capability_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_capability_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_capability_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_capability_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Capability Specification

## Scenarios

### Backend Capability

#### names the backend and unsupported async operation in C lowering

- LocalId
- LocalId
- MirType promise
   - Expected: output does not contain `not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

-  1 translate receive
   - Expected: output does not contain `Instruction not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- LocalId
- mir operand copy
- mir operand copy
   - Expected: output does not contain `@__simple_runtime_matmul`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Some
- mir operand const int
- mir operand copy
- mir operand const int
- mir operand copy
   - Expected: output does not contain `@__simple_intrinsic___simple_ssa_phi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- LocalId
- mir operand copy
   - Expected: output does not contain `Instruction not implemented`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(vhdl_compile_match_u8()).to_contain("case opcode is")
expect(vhdl_compile_clocked_process()).to_contain("rising_edge(clk)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/backend_capability_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend Capability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
