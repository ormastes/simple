# Var Reassign Analysis Specification

> Tests covering var reassignment analysis.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Var Reassign Analysis Specification

## Scenarios

### var reassignment analysis

#### keeps intrinsics while lowering reassigned locals through stack slots

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps intrinsics while lowering reassigned locals through stack slots
   - Expected: result.applied is true
   - Expected: result.reason equals `ready`
   - Expected: name equals `bounds_check`
   - Expected: dest != nil is true
   - Expected: dest.unwrap().id equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps intrinsics while lowering reassigned locals through stack slots")
val entry = MirBlock(
    id: BlockId.new(0),
    label: "entry",
    instructions: [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Intrinsic(nil, "bounds_check", [copy_operand(0)]))
    ],
    terminator: MirTerminator.Goto(BlockId.new(1))
)
val next = MirBlock(
    id: BlockId.new(1),
    label: "next",
    instructions: [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64())),
        inst(MirInstKind.Intrinsic(Some(local(0)), "probe", [copy_operand(0)]))
    ],
    terminator: MirTerminator.Ret(Some(copy_operand(0)))
)
val locals = [MirLocal(id: local(0), name: nil, type_: MirType.i64(), kind: LocalKind.Var, is_ghost: false)]
val result = ssa_alloca_transform_blocks([entry, next], locals, BlockId.entry())

expect(result.applied).to_equal(true)
expect(result.reason).to_equal("ready")
match result.blocks[0].instructions[4].kind:
    case Intrinsic(_, name, args):
        expect(name).to_equal("bounds_check")
        match args[0].kind:
            case Copy(loaded): expect(loaded.id).to_equal(3)
            case _: fail("intrinsic operand was not loaded from the reassigned local slot")
    case _: fail("intrinsic was removed by the alloca transform")
match result.blocks[1].instructions[3].kind:
    case Intrinsic(dest, _, args):
        expect(dest != nil).to_equal(true)
        expect(dest.unwrap().id).to_equal(6)
        match args[0].kind:
            case Copy(loaded): expect(loaded.id).to_equal(5)
            case _: fail("intrinsic operand was not loaded before destination rewrite")
    case _: fail("intrinsic destination was not preserved by the alloca transform")
```

</details>

#### preserves present and nil optional destinations through alloca operand rewriting

- preserves present and nil optional destinations through alloca operand rewriting


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves present and nil optional destinations through alloca operand rewriting")
val sig = MirSignature(params: [], return_type: MirType.i64(), is_variadic: false)
val present = [
    MirInstKind.Call(Some(local(0)), int_operand(90), [copy_operand(0)]),
    MirInstKind.CallIndirect(Some(local(0)), int_operand(91), [copy_operand(0)], sig),
    MirInstKind.Intrinsic(Some(local(0)), "optional_dest", [copy_operand(0)])
]
for kind in present:
    expect_optional_dest_alloca_rewrite(kind, true)

val absent = [
    MirInstKind.Call(nil, int_operand(90), [copy_operand(0)]),
    MirInstKind.CallIndirect(nil, int_operand(91), [copy_operand(0)], sig),
    MirInstKind.Intrinsic(nil, "optional_dest", [copy_operand(0)])
]
for kind in absent:
    expect_optional_dest_alloca_rewrite(kind, false)
```

</details>

#### rejects a nil local nested in a call-indirect move operand

- rejects a nil local nested in a call-indirect move operand
   - Expected: result.applied is false
   - Expected: result.reason equals `unsupported instruction`
   - Expected: result.blocks[0].instructions.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a nil local nested in a call-indirect move operand")
val sig = MirSignature(params: [], return_type: MirType.i64(), is_variadic: false)
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64())),
        inst(MirInstKind.CallIndirect(nil, int_operand(91), [MirOperand(kind: MirOperandKind.Move(nil))], sig))
    ],
    MirTerminator.Ret(nil)
)
val locals = [MirLocal(id: local(0), name: nil, type_: MirType.i64(), kind: LocalKind.Var, is_ghost: false)]
val result = ssa_alloca_transform_blocks(blocks, locals, BlockId.entry())

expect(result.applied).to_equal(false)
expect(result.reason).to_equal("unsupported instruction")
expect(result.blocks[0].instructions.len()).to_equal(3)
```

</details>

#### marks repeated local definitions as SSA-transformable when local and borrow-safe

- marks repeated local definitions as SSA-transformable when local and borrow-safe
   - Expected: analysis.has_var_reassignment is true
   - Expected: analysis.reassignment_count equals `1`
   - Expected: analysis.ssa_transform_safe is true
   - Expected: analysis.no_escape is true
   - Expected: analysis.borrow_reassign_safe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks repeated local definitions as SSA-transformable when local and borrow-safe")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))
    ],
    MirTerminator.Ret(Some(copy_operand(1)))
)
val analysis = analyze_var_reassign_blocks(blocks)
expect(analysis.has_var_reassignment).to_equal(true)
expect(analysis.reassignment_count).to_equal(1)
expect(analysis.ssa_transform_safe).to_equal(true)
expect(analysis.no_escape).to_equal(true)
expect(analysis.borrow_reassign_safe).to_equal(true)
```

</details>

#### rejects reassignment after an outstanding borrow of the same local

- rejects reassignment after an outstanding borrow of the same local
   - Expected: analysis.has_var_reassignment is true
   - Expected: analysis.ssa_transform_safe is false
   - Expected: analysis.borrow_reassign_safe is false
   - Expected: analysis.reason equals `borrow.reassign_unsafe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects reassignment after an outstanding borrow of the same local")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Ref(local(2), MirBorrowKind.Shared, MirPlace.local_place(local(0)))),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))
    ],
    MirTerminator.Ret(Some(copy_operand(2)))
)
val analysis = analyze_var_reassign_blocks(blocks)
expect(analysis.has_var_reassignment).to_equal(true)
expect(analysis.ssa_transform_safe).to_equal(false)
expect(analysis.borrow_reassign_safe).to_equal(false)
expect(analysis.reason).to_equal("borrow.reassign_unsafe")
```

</details>

#### rejects reassigned locals that escape through return

- rejects reassigned locals that escape through return
   - Expected: analysis.has_var_reassignment is true
   - Expected: analysis.no_escape is false
   - Expected: analysis.ssa_transform_safe is false
   - Expected: analysis.reason equals `escape.reassigned_storage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects reassigned locals that escape through return")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))
    ],
    MirTerminator.Ret(Some(copy_operand(0)))
)
val analysis = analyze_var_reassign_blocks(blocks)
expect(analysis.has_var_reassignment).to_equal(true)
expect(analysis.no_escape).to_equal(false)
expect(analysis.ssa_transform_safe).to_equal(false)
expect(analysis.reason).to_equal("escape.reassigned_storage")
```

</details>

#### rejects reassigned locals that escape through a copied alias

- rejects reassigned locals that escape through a copied alias
   - Expected: analysis.has_var_reassignment is true
   - Expected: analysis.no_escape is false
   - Expected: analysis.ssa_transform_safe is false
   - Expected: analysis.reason equals `escape.reassigned_storage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects reassigned locals that escape through a copied alias")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64())),
        inst(MirInstKind.Copy(local(2), local(0)))
    ],
    MirTerminator.Ret(Some(copy_operand(2)))
)
val analysis = analyze_var_reassign_blocks(blocks)
expect(analysis.has_var_reassignment).to_equal(true)
expect(analysis.no_escape).to_equal(false)
expect(analysis.ssa_transform_safe).to_equal(false)
expect(analysis.reason).to_equal("escape.reassigned_storage")
```

</details>

#### rejects reassignment after a borrow through a copied alias

- rejects reassignment after a borrow through a copied alias
   - Expected: analysis.has_var_reassignment is true
   - Expected: analysis.borrow_reassign_safe is false
   - Expected: analysis.ssa_transform_safe is false
   - Expected: analysis.reason equals `borrow.reassign_unsafe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects reassignment after a borrow through a copied alias")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Copy(local(2), local(0))),
        inst(MirInstKind.Ref(local(3), MirBorrowKind.Shared, MirPlace.local_place(local(2)))),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))
    ],
    MirTerminator.Ret(Some(copy_operand(3)))
)
val analysis = analyze_var_reassign_blocks(blocks)
expect(analysis.has_var_reassignment).to_equal(true)
expect(analysis.borrow_reassign_safe).to_equal(false)
expect(analysis.ssa_transform_safe).to_equal(false)
expect(analysis.reason).to_equal("borrow.reassign_unsafe")
```

</details>

#### feeds analyzer output into JIT var hotspot planning

- feeds analyzer output into JIT var hotspot planning
   - Expected: plan.eligible is true
   - Expected: plan.facts contains `ssa.var_transform`
   - Expected: plan.facts contains `borrow.reassign_safe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("feeds analyzer output into JIT var hotspot planning")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))
    ],
    MirTerminator.Ret(Some(copy_operand(1)))
)
val analysis = analyze_var_reassign_blocks(blocks)
val facts = var_reassign_analysis_to_jit_facts(analysis)
val plan = jit_hotspot_plan_with_var_facts(hot_profile(), hotspot_config(), true, true, facts)
expect(plan.eligible).to_equal(true)
expect(plan.facts.contains("ssa.var_transform")).to_equal(true)
expect(plan.facts.contains("borrow.reassign_safe")).to_equal(true)
```

</details>

#### builds hotspot proof facts from var reassignment analysis

- builds hotspot proof facts from var reassignment analysis
   - Expected: facts contains `typed_mir`
   - Expected: facts contains `safe_deopt`
   - Expected: facts contains `ssa.var_transform`
   - Expected: facts contains `escape.analyzed`
   - Expected: facts contains `escape.no_escape`
   - Expected: facts contains `borrow.reassign_safe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds hotspot proof facts from var reassignment analysis")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))
    ],
    MirTerminator.Ret(Some(copy_operand(1)))
)
val analysis = analyze_var_reassign_blocks(blocks)
val facts = var_reassign_analysis_hotspot_facts(["typed_mir", "safe_deopt"], analysis)
expect(facts.contains("typed_mir")).to_equal(true)
expect(facts.contains("safe_deopt")).to_equal(true)
expect(facts.contains("ssa.var_transform")).to_equal(true)
expect(facts.contains("escape.analyzed")).to_equal(true)
expect(facts.contains("escape.no_escape")).to_equal(true)
expect(facts.contains("borrow.reassign_safe")).to_equal(true)
```

</details>

#### creates MIR analysis-backed hotspot specialization providers only after SSA proof

- creates MIR analysis-backed hotspot specialization providers only after SSA proof
   - Expected: provider.semantic_proof is true
   - Expected: provider.specialized_source equals `fn hot_var() -> i64: 3`
   - Expected: decision.provider_used is true
   - Expected: decision.compile_source equals `fn hot_var() -> i64: 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates MIR analysis-backed hotspot specialization providers only after SSA proof")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64())),
        inst(MirInstKind.BinOp(local(1), MirBinOp.Add, copy_operand(0), int_operand(1)))
    ],
    MirTerminator.Ret(Some(copy_operand(1)))
)
val provider = jit_hotspot_specialization_provider_from_var_reassign_analysis(
    "mir-var-specialization",
    "fn hot_var() -> i64: 3",
    blocks,
    ["typed_mir", "safe_deopt"]
)
val analysis = analyze_var_reassign_blocks(blocks)
val facts = var_reassign_analysis_to_jit_facts(analysis)
val plan = jit_hotspot_plan_with_var_facts(hot_profile(), hotspot_config(), true, true, facts)
val decision = jit_hotspot_consume_plan_with_provider(plan, hot_profile().source, provider)
expect(provider.semantic_proof).to_equal(true)
expect(provider.specialized_source).to_equal("fn hot_var() -> i64: 3")
expect(decision.provider_used).to_equal(true)
expect(decision.compile_source).to_equal("fn hot_var() -> i64: 3")
```

</details>

#### rejects MIR analysis-backed providers when SSA transform is unsafe

- rejects MIR analysis-backed providers when SSA transform is unsafe
   - Expected: provider.semantic_proof is false
   - Expected: provider.specialized_source equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects MIR analysis-backed providers when SSA transform is unsafe")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Ref(local(2), MirBorrowKind.Shared, MirPlace.local_place(local(0)))),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))
    ],
    MirTerminator.Ret(Some(copy_operand(2)))
)
val provider = jit_hotspot_specialization_provider_from_var_reassign_analysis(
    "mir-var-specialization",
    "fn hot_var() -> i64: 3",
    blocks,
    ["typed_mir", "safe_deopt"]
)
expect(provider.semantic_proof).to_equal(false)
expect(provider.specialized_source).to_equal("")
```

</details>

#### rewrites straight-line reassignment into a fresh SSA local

- rewrites straight-line reassignment into a fresh SSA local
   - Expected: result.applied is true
   - Expected: result.renamed_count equals `1`
   - Expected: dest.id equals `2`
   - Expected: local_id.id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rewrites straight-line reassignment into a fresh SSA local")
val blocks = one_block(
    [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64())),
        inst(MirInstKind.BinOp(local(1), MirBinOp.Add, copy_operand(0), int_operand(1)))
    ],
    MirTerminator.Ret(Some(copy_operand(1)))
)
val result = ssa_var_transform_blocks(blocks)
expect(result.applied).to_equal(true)
expect(result.renamed_count).to_equal(1)
val rewritten = result.blocks[0].instructions
match rewritten[1].kind:
    case Const(dest, _, _):
        expect(dest.id).to_equal(2)
    case _:
        fail("unexpected MIR rewrite shape")
match rewritten[2].kind:
    case BinOp(_, _, left, _):
        match left.kind:
            case Copy(local_id):
                expect(local_id.id).to_equal(2)
            case _:
                fail("unexpected MIR rewrite shape")
    case _:
        fail("unexpected MIR rewrite shape")
```

</details>

#### reports unsupported CFG when no simple phi merge is recognized

- reports unsupported CFG when no simple phi merge is recognized
   - Expected: result.applied is false
   - Expected: result.reason equals `unsupported cfg`
   - Expected: result.phi_required_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports unsupported CFG when no simple phi merge is recognized")
val first = MirBlock(
    id: BlockId.new(0),
    label: "entry",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(1))
)
val second = MirBlock(
    id: BlockId.new(1),
    label: "next",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))],
    terminator: MirTerminator.Ret(Some(copy_operand(0)))
)
val result = ssa_var_transform_blocks([first, second])
expect(result.applied).to_equal(false)
expect(result.reason).to_equal("unsupported cfg")
expect(result.phi_required_count).to_equal(0)
```

</details>

#### applies pseudo-phi SSA transform for a safe if/else merge

- applies pseudo-phi SSA transform for a safe if/else merge
   - Expected: result.applied is true
   - Expected: result.reason equals `ready`
   - Expected: result.renamed_count equals `1`
   - Expected: result.phi_required_count equals `0`
   - Expected: dest != nil is true
   - Expected: name equals `__simple_ssa_phi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("applies pseudo-phi SSA transform for a safe if/else merge")
val entry = MirBlock(
    id: BlockId.new(0),
    label: "entry",
    instructions: [],
    terminator: MirTerminator.If(copy_operand(9), BlockId.new(1), BlockId.new(2))
)
val then_block = MirBlock(
    id: BlockId.new(1),
    label: "then",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val else_block = MirBlock(
    id: BlockId.new(2),
    label: "else",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val join = MirBlock(
    id: BlockId.new(3),
    label: "join",
    instructions: [inst(MirInstKind.BinOp(local(1), MirBinOp.Add, copy_operand(0), int_operand(1)))],
    terminator: MirTerminator.Ret(Some(copy_operand(1)))
)
val result = ssa_var_transform_blocks([entry, then_block, else_block, join])
expect(result.applied).to_equal(true)
expect(result.reason).to_equal("ready")
expect(result.renamed_count).to_equal(1)
expect(result.phi_required_count).to_equal(0)
match result.blocks[3].instructions[0].kind:
    case Intrinsic(dest, name, _):
        expect(dest != nil).to_equal(true)
        expect(name).to_equal("__simple_ssa_phi")
    case _:
        fail("unexpected MIR rewrite shape")
```

</details>

#### returns the pseudo-phi value when an if/else merge returns the reassigned var

- returns the pseudo-phi value when an if/else merge returns the reassigned var
   - Expected: result.applied is true
   - Expected: result.reason equals `ready`
   - Expected: value != nil is true
   - Expected: local_id.id equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns the pseudo-phi value when an if/else merge returns the reassigned var")
val entry = MirBlock(
    id: BlockId.new(0),
    label: "entry",
    instructions: [],
    terminator: MirTerminator.If(copy_operand(9), BlockId.new(1), BlockId.new(2))
)
val then_block = MirBlock(
    id: BlockId.new(1),
    label: "then",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val else_block = MirBlock(
    id: BlockId.new(2),
    label: "else",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val join = MirBlock(
    id: BlockId.new(3),
    label: "join",
    instructions: [],
    terminator: MirTerminator.Ret(Some(copy_operand(0)))
)
val result = ssa_var_transform_blocks([entry, then_block, else_block, join])
expect(result.applied).to_equal(true)
expect(result.reason).to_equal("ready")
match result.blocks[3].terminator:
    case Ret(value):
        expect(value != nil).to_equal(true)
        match value.unwrap().kind:
            case Copy(local_id):
                expect(local_id.id).to_equal(12)
            case _:
                fail("unexpected MIR rewrite shape")
    case _:
        fail("unexpected MIR rewrite shape")
```

</details>

#### rejects if/else phi transform when a branch reassignment violates borrow safety

- rejects if/else phi transform when a branch reassignment violates borrow safety
   - Expected: result.applied is false
   - Expected: result.reason equals `borrow.reassign_unsafe`
   - Expected: result.phi_required_count equals `1`
   - Expected: result.phi_required_locals[0] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects if/else phi transform when a branch reassignment violates borrow safety")
val entry = MirBlock(
    id: BlockId.new(0),
    label: "entry",
    instructions: [],
    terminator: MirTerminator.If(copy_operand(9), BlockId.new(1), BlockId.new(2))
)
val then_block = MirBlock(
    id: BlockId.new(1),
    label: "then",
    instructions: [
        inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64())),
        inst(MirInstKind.Ref(local(5), MirBorrowKind.Shared, MirPlace.local_place(local(0)))),
        inst(MirInstKind.Const(local(0), MirConstValue.Int(3), MirType.i64()))
    ],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val else_block = MirBlock(
    id: BlockId.new(2),
    label: "else",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val join = MirBlock(
    id: BlockId.new(3),
    label: "join",
    instructions: [inst(MirInstKind.BinOp(local(1), MirBinOp.Add, copy_operand(0), int_operand(1)))],
    terminator: MirTerminator.Ret(Some(copy_operand(1)))
)
val result = ssa_var_transform_blocks([entry, then_block, else_block, join])
expect(result.applied).to_equal(false)
expect(result.reason).to_equal("borrow.reassign_unsafe")
expect(result.phi_required_count).to_equal(1)
expect(result.phi_required_locals[0]).to_equal(0)
```

</details>

#### builds a concrete phi insertion plan for an if/else merge

- builds a concrete phi insertion plan for an if/else merge
   - Expected: plans.len() equals `1`
   - Expected: plans[0].join_block_id equals `3`
   - Expected: plans[0].original_local_id equals `0`
   - Expected: plans[0].then_block_id equals `1`
   - Expected: plans[0].else_block_id equals `2`
   - Expected: plans[0].then_value_local_id equals `10`
   - Expected: plans[0].else_value_local_id equals `11`
   - Expected: plans[0].phi_dest_local_id equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds a concrete phi insertion plan for an if/else merge")
val entry = MirBlock(
    id: BlockId.new(0),
    label: "entry",
    instructions: [],
    terminator: MirTerminator.If(copy_operand(9), BlockId.new(1), BlockId.new(2))
)
val then_block = MirBlock(
    id: BlockId.new(1),
    label: "then",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val else_block = MirBlock(
    id: BlockId.new(2),
    label: "else",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val join = MirBlock(
    id: BlockId.new(3),
    label: "join",
    instructions: [inst(MirInstKind.BinOp(local(1), MirBinOp.Add, copy_operand(0), int_operand(1)))],
    terminator: MirTerminator.Ret(Some(copy_operand(1)))
)
val plans = ssa_phi_plans_for_blocks([entry, then_block, else_block, join])
expect(plans.len()).to_equal(1)
expect(plans[0].join_block_id).to_equal(3)
expect(plans[0].original_local_id).to_equal(0)
expect(plans[0].then_block_id).to_equal(1)
expect(plans[0].else_block_id).to_equal(2)
expect(plans[0].then_value_local_id).to_equal(10)
expect(plans[0].else_value_local_id).to_equal(11)
expect(plans[0].phi_dest_local_id).to_equal(12)
```

</details>

#### materializes a pseudo phi intrinsic for an if/else merge

- materializes a pseudo phi intrinsic for an if/else merge
   - Expected: result.applied is true
   - Expected: result.phi_count equals `1`
   - Expected: dest.id equals `10`
   - Expected: dest.id equals `11`
   - Expected: dest != nil is true
   - Expected: dest.unwrap().id equals `12`
   - Expected: name equals `__simple_ssa_phi`
   - Expected: v equals `1`
   - Expected: local_id.id equals `10`
   - Expected: v equals `2`
   - Expected: local_id.id equals `11`
   - Expected: local_id.id equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 85 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("materializes a pseudo phi intrinsic for an if/else merge")
val entry = MirBlock(
    id: BlockId.new(0),
    label: "entry",
    instructions: [],
    terminator: MirTerminator.If(copy_operand(9), BlockId.new(1), BlockId.new(2))
)
val then_block = MirBlock(
    id: BlockId.new(1),
    label: "then",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(1), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val else_block = MirBlock(
    id: BlockId.new(2),
    label: "else",
    instructions: [inst(MirInstKind.Const(local(0), MirConstValue.Int(2), MirType.i64()))],
    terminator: MirTerminator.Goto(BlockId.new(3))
)
val join = MirBlock(
    id: BlockId.new(3),
    label: "join",
    instructions: [inst(MirInstKind.BinOp(local(1), MirBinOp.Add, copy_operand(0), int_operand(1)))],
    terminator: MirTerminator.Ret(Some(copy_operand(1)))
)
val result = ssa_materialize_phi_plans_for_blocks([entry, then_block, else_block, join])
expect(result.applied).to_equal(true)
expect(result.phi_count).to_equal(1)

match result.blocks[1].instructions[0].kind:
    case Const(dest, _, _):
        expect(dest.id).to_equal(10)
    case _:
        fail("unexpected MIR rewrite shape")
match result.blocks[2].instructions[0].kind:
    case Const(dest, _, _):
        expect(dest.id).to_equal(11)
    case _:
        fail("unexpected MIR rewrite shape")
match result.blocks[3].instructions[0].kind:
    case Intrinsic(dest, name, args):
        expect(dest != nil).to_equal(true)
        if dest:
            expect(dest.unwrap().id).to_equal(12)
        expect(name).to_equal("__simple_ssa_phi")
        match args[0].kind:
            case Const(value, _):
                match value:
                    case Int(v):
                        expect(v).to_equal(1)
                    case _:
                        fail("unexpected MIR rewrite shape")
            case _:
                fail("unexpected MIR rewrite shape")
        match args[1].kind:
            case Copy(local_id):
                expect(local_id.id).to_equal(10)
            case _:
                fail("unexpected MIR rewrite shape")
        match args[2].kind:
            case Const(value, _):
                match value:
                    case Int(v):
                        expect(v).to_equal(2)
                    case _:
                        fail("unexpected MIR rewrite shape")
            case _:
                fail("unexpected MIR rewrite shape")
        match args[3].kind:
            case Copy(local_id):
                expect(local_id.id).to_equal(11)
            case _:
                fail("unexpected MIR rewrite shape")
    case _:
        fail("unexpected MIR rewrite shape")
match result.blocks[3].instructions[1].kind:
    case BinOp(_, _, left, _):
        match left.kind:
            case Copy(local_id):
                expect(local_id.id).to_equal(12)
            case _:
                fail("unexpected MIR rewrite shape")
    case _:
        fail("unexpected MIR rewrite shape")
```

</details>

#### declares backend lowering policy for pseudo phi materialization for REQ-OPJH-021

- declares backend lowering policy for pseudo phi materialization for REQ-OPJH-021
   - Expected: cranelift.can_lower is true
   - Expected: ssa_phi_lowering_kind_name(cranelift.lowering_kind) equals `cranelift_block_param`
   - Expected: cranelift.reason equals `lower_to_block_params`
   - Expected: alias.backend_name equals `cranelift`
   - Expected: ssa_phi_lowering_kind_name(alias.lowering_kind) equals `cranelift_block_param`
   - Expected: llvm.can_lower is true
   - Expected: ssa_phi_lowering_kind_name(llvm.lowering_kind) equals `llvm_phi_node`
   - Expected: llvm.reason equals `lower_to_phi_nodes`
   - Expected: llvm_alias.backend_name equals `llvm`
   - Expected: ssa_phi_lowering_kind_name(llvm_alias.lowering_kind) equals `llvm_phi_node`
   - Expected: ssa_phi_backend_can_lower("llvmlib") is true
   - Expected: interpreter.can_lower is true
   - Expected: ssa_phi_lowering_kind_name(interpreter.lowering_kind) equals `interpreter_fallback`
   - Expected: unsupported.can_lower is false
   - Expected: ssa_phi_lowering_kind_name(unsupported.lowering_kind) equals `unsupported`
   - Expected: ssa_phi_backend_can_lower("wasm") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares backend lowering policy for pseudo phi materialization for REQ-OPJH-021")
val cranelift = ssa_phi_lowering_policy_for_backend("cranelift")
expect(cranelift.can_lower).to_equal(true)
expect(ssa_phi_lowering_kind_name(cranelift.lowering_kind)).to_equal("cranelift_block_param")
expect(cranelift.reason).to_equal("lower_to_block_params")

val alias = ssa_phi_lowering_policy_for_backend("cranlift")
expect(alias.backend_name).to_equal("cranelift")
expect(ssa_phi_lowering_kind_name(alias.lowering_kind)).to_equal("cranelift_block_param")

val llvm = ssa_phi_lowering_policy_for_backend("llvm")
expect(llvm.can_lower).to_equal(true)
expect(ssa_phi_lowering_kind_name(llvm.lowering_kind)).to_equal("llvm_phi_node")
expect(llvm.reason).to_equal("lower_to_phi_nodes")

val llvm_alias = ssa_phi_lowering_policy_for_backend("llvm-lib")
expect(llvm_alias.backend_name).to_equal("llvm")
expect(ssa_phi_lowering_kind_name(llvm_alias.lowering_kind)).to_equal("llvm_phi_node")
expect(ssa_phi_backend_can_lower("llvmlib")).to_equal(true)

val interpreter = ssa_phi_lowering_policy_for_backend("interpreter")
expect(interpreter.can_lower).to_equal(true)
expect(ssa_phi_lowering_kind_name(interpreter.lowering_kind)).to_equal("interpreter_fallback")

val unsupported = ssa_phi_lowering_policy_for_backend("c")
expect(unsupported.can_lower).to_equal(false)
expect(ssa_phi_lowering_kind_name(unsupported.lowering_kind)).to_equal("unsupported")
expect(ssa_phi_backend_can_lower("wasm")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering var reassignment analysis.
- var reassignment analysis

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

- `REQ-SSPEC-COMPILER`
- `REQ-OPJH-021":`
- `REQ-OPJH-021")`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58343d4fb1f9b16a80b8c458ef844278a198313e5c87474df3a640c81e2e1c4a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58343d4fb1f9b16a80b8c458ef844278a198313e5c87474df3a640c81e2e1c4a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58343d4fb1f9b16a80b8c458ef844278a198313e5c87474df3a640c81e2e1c4a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/var_reassign_analysis_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/var_reassign_analysis_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/var_reassign_analysis_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 31 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps intrinsics while lowering reassigned locals through stack slots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves present and nil optional destinations through alloca operand rewriting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/var_reassign_analysis_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a nil local nested in a call-indirect move operand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
