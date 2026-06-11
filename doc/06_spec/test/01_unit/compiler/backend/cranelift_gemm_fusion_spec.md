# Cranelift Gemm Fusion Specification

> <details>

<!-- sdn-diagram:id=cranelift_gemm_fusion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cranelift_gemm_fusion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cranelift_gemm_fusion_spec -> std
cranelift_gemm_fusion_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cranelift_gemm_fusion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cranelift Gemm Fusion Specification

## Scenarios

### Cranelift GEMM-add fusion detection

#### detects adjacent MatMul consumed once by BroadcastAdd

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matmul = binop_inst(3, MirBinOp.MatMul, 0, 1)
val add = binop_inst(4, MirBinOp.BroadcastAdd, 3, 2)
val func = test_func([matmul, add], MirTerminator.Return(Some(copy_operand(4))))

val plan = detect_gemm_add_pair(func, matmul, add)
expect(plan.?).to_equal(true)
if plan.?:
    expect(plan.unwrap().dest.id).to_equal(4)
```

</details>

#### does not fuse when the MatMul temp has a second use

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matmul = binop_inst(3, MirBinOp.MatMul, 0, 1)
val add = binop_inst(4, MirBinOp.BroadcastAdd, 3, 2)
val extra_use = MirInst(kind: MirInstKind.Copy(LocalId(id: 5), LocalId(id: 3)), span: nil)
val func = test_func([matmul, add, extra_use], MirTerminator.Return(Some(copy_operand(4))))

val plan = detect_gemm_add_pair(func, matmul, add)
expect(plan.?).to_equal(false)
```

</details>

#### does not fuse non-add broadcast operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matmul = binop_inst(3, MirBinOp.MatMul, 0, 1)
val sub = binop_inst(4, MirBinOp.BroadcastSub, 3, 2)
val func = test_func([matmul, sub], MirTerminator.Return(Some(copy_operand(4))))

val plan = detect_gemm_add_pair(func, matmul, sub)
expect(plan.?).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/cranelift_gemm_fusion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Cranelift GEMM-add fusion detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
