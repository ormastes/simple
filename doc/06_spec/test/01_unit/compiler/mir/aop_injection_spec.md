# Aop Injection Specification

> 1. MirConstValue Str

<!-- sdn-diagram:id=aop_injection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_injection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_injection_spec -> std
aop_injection_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_injection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Injection Specification

## Scenarios

### MIR AOP Injection

### classify_mir_inst_kind

#### classifies Call as call

1. MirConstValue Str
2. MirType
   - Expected: classify_mir_inst_kind(kind) equals `call`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func_op = MirOperand(kind: MirOperandKind.Const(
    MirConstValue.Str("test_fn"),
    MirType(kind: MirTypeKind.FuncPtr(MirSignature(params: [], return_type: MirType.unit(), is_variadic: false)))
))
val kind = MirInstKind.Call(nil, func_op, [])
expect(classify_mir_inst_kind(kind)).to_equal("call")
```

</details>

#### classifies Store as assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = MirOperand(kind: MirOperandKind.Copy(LocalId(0)))
val value = MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), MirType.i64()))
val kind = MirInstKind.Store(ptr, value)
expect(classify_mir_inst_kind(kind)).to_equal("assignment")
```

</details>

#### classifies comparison BinOp as comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), MirType.i64()))
val right = MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(2), MirType.i64()))
val kind = MirInstKind.BinOp(LocalId(0), MirBinOp.Eq, left, right)
expect(classify_mir_inst_kind(kind)).to_equal("comparison")
```

</details>

### make_advice_call_inst

#### creates a valid MIR Call instruction

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = make_advice_call_inst("my_advice")
match inst.kind:
    case Call(dest, func, args):
        expect(dest == nil).to_equal(true)
        expect(args.len()).to_equal(0)
    case _:
        fail("expected injected MIR call")
```

</details>

### extract_mir_block_info

#### converts empty block list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks: [MirBlock] = []
val infos = extract_mir_block_info(blocks)
expect(infos.len()).to_equal(0)
```

</details>

#### converts block with instructions

1. id: BlockId
2. terminator: MirTerminator Ret
   - Expected: infos.len() equals `1`
   - Expected: infos[0].instruction_kinds.len() equals `1`
   - Expected: infos[0].instruction_kinds[0].kind_tag equals `call`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = make_advice_call_inst("test_fn")
val block = MirBlock(
    id: BlockId(0),
    label: nil,
    instructions: [inst],
    terminator: MirTerminator.Ret(nil)
)
val infos = extract_mir_block_info([block])
expect(infos.len()).to_equal(1)
expect(infos[0].instruction_kinds.len()).to_equal(1)
expect(infos[0].instruction_kinds[0].kind_tag).to_equal("call")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/aop_injection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MIR AOP Injection
- classify_mir_inst_kind
- make_advice_call_inst
- extract_mir_block_info

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
