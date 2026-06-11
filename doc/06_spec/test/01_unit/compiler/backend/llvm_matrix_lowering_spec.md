# Llvm Matrix Lowering Specification

> 1. kind: MirInstKind BinOp

<!-- sdn-diagram:id=llvm_matrix_lowering_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llvm_matrix_lowering_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llvm_matrix_lowering_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llvm_matrix_lowering_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llvm Matrix Lowering Specification

## Scenarios

### LLVM matrix lowering

#### fails explicitly for MatMul and BroadcastAdd instead of emitting unresolved runtime calls

1. kind: MirInstKind BinOp
2. kind: MirInstKind BinOp


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_matrix_module("matrix_ops", [
    MirInst(
        kind: MirInstKind.BinOp(LocalId(id: 2), MirBinOp.MatMul, copy_of(0), copy_of(1)),
        span: nil
    ),
    MirInst(
        kind: MirInstKind.BinOp(LocalId(id: 2), MirBinOp.BroadcastAdd, copy_of(0), copy_of(1)),
        span: nil
    )
])

val output = translate(module)

expect(output).to_contain("LLVM backend does not support MatMul lowering")
expect(output).to_contain("LLVM backend does not support BroadcastAdd lowering")
expect(output).to_not_contain("@__simple_runtime_matmul")
expect(output).to_not_contain("@__simple_runtime_broadcast_add")
```

</details>

#### fails explicitly for Transpose instead of emitting an unresolved runtime call

1. kind: MirInstKind UnaryOp


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = make_matrix_module("transpose_op", [
    MirInst(
        kind: MirInstKind.UnaryOp(LocalId(id: 2), MirUnaryOp.Transpose, copy_of(0)),
        span: nil
    )
])

val output = translate(module)

expect(output).to_contain("LLVM backend does not support Transpose lowering")
expect(output).to_not_contain("@__simple_runtime_transpose")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/llvm_matrix_lowering_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLVM matrix lowering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
