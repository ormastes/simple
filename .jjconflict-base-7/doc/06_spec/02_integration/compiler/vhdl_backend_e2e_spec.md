# vhdl_backend_e2e_spec

> @cover src/compiler/70.backend/backend/vhdl_backend.spl 80%

<!-- sdn-diagram:id=vhdl_backend_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_backend_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_backend_e2e_spec -> compiler
vhdl_backend_e2e_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_backend_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vhdl_backend_e2e_spec

@cover src/compiler/70.backend/backend/vhdl_backend.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #vhdl-backend, #ghdl-validation |
| Category | Integration |
| Difficulty | 4/5 |
| Status | Active |
| Source | `test/02_integration/compiler/vhdl_backend_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/compiler/70.backend/backend/vhdl_backend.spl 80%
VHDL Backend End-to-End Integration Tests

Tests the complete VHDL backend pipeline: MIR construction → VhdlBackend.compile()
→ VHDL output → GHDL analysis/elaboration validation.

These tests verify that backend-generated VHDL is accepted by a real
VHDL-2008 toolchain (GHDL), not just structurally plausible text.

## Scenarios

### VHDL Backend E2E - Entity Generation

#### compiles simple adder to valid VHDL entity

1. make arg local
2. make arg local
3. make return local
4. make temp local
5. LocalId
6. MirOperand
7. MirOperand
8. span: empty span
9. kind: MirInstKind Copy
10. span: empty span
11. id: BlockId
12. check msg
13. check
14. check
15. check
16. check
17. check
18. check
19. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

# Build a simple add function: fn add(a: i32, b: i32) -> i32
val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_arg_local(1, 1, "b", make_i32()),
    make_return_local(2, make_i32()),
    make_temp_local(3, "sum", make_i32())
]

val add_inst = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 3),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))
    ),
    span: empty_span()
)

val assign_inst = MirInst(
    kind: MirInstKind.Copy(LocalId(id: 2), LocalId(id: 3)),
    span: empty_span()
)

val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [add_inst, assign_inst],
    terminator: nil
)

val func = make_function("adder", [make_i32(), make_i32()], make_i32(), locals, [block])
val module = make_module("adder_module", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed")

val compiled = result.unwrap()
val vhdl = compiled.vhdl

# Structural checks
check(vhdl.contains("library ieee;"))
check(vhdl.contains("entity adder is"))
check(vhdl.contains("architecture rtl of adder is"))
check(vhdl.contains("a : in signed(31 downto 0)"))
check(vhdl.contains("b : in signed(31 downto 0)"))
check(vhdl.contains("result_out : out signed(31 downto 0)"))
check(vhdl.contains("sum <= a + b;"))
```

</details>

#### compiles boolean comparison to valid VHDL

1. make arg local
2. make arg local
3. make return local
4. LocalId
5. MirOperand
6. MirOperand
7. span: empty span
8. id: BlockId
9. check msg
10. check
11. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

# fn compare(a: i32, b: i32) -> bool
val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_arg_local(1, 1, "b", make_i32()),
    make_return_local(2, make_bool())
]

val cmp_inst = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 2),
        MirBinOp.Eq,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))
    ),
    span: empty_span()
)

val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [cmp_inst],
    terminator: nil
)

val func = make_function("comparator", [make_i32(), make_i32()], make_bool(), locals, [block])
val module = make_module("cmp_module", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for comparator")

val compiled = result.unwrap()
check(compiled.vhdl.contains("entity comparator is"))
check(compiled.vhdl.contains("result_out : out bit"))
```

</details>

#### compiles local copies to signal assignments

1. make arg local
2. make return local
3. make temp local
4. MirLocal
5. LocalId
6. MirOperand
7. MirOperand
8. span: empty span
9. kind: MirInstKind Copy
10. span: empty span
11. kind: MirInstKind Copy
12. span: empty span
13. check msg
14. check
15. check
16. check
17. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

# MIR shape for: tmp = a + 1; x = tmp; return x
val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_return_local(1, make_i32()),
    make_temp_local(2, "tmp", make_i32()),
    MirLocal(id: LocalId(id: 3), name: Some("x"), type_: make_i32(), kind: LocalKind.Var)
]

val add_inst = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 2),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val store_inst = MirInst(
    kind: MirInstKind.Copy(LocalId(id: 3), LocalId(id: 2)),
    span: empty_span()
)
val load_inst = MirInst(
    kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 3)),
    span: empty_span()
)

val block = MirBlock(id: BlockId(id: 0), instructions: [add_inst, store_inst, load_inst], terminator: nil)
val func = make_function("local_store", [make_i32()], make_i32(), locals, [block])
val module = make_module("local_store_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for local copies")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("signal x : signed(31 downto 0);"))
check(vhdl.contains("tmp <= a + to_signed(1, 32);"))
check(vhdl.contains("x <= tmp;"))
check(vhdl.contains("result_out <= x;"))
```

</details>

#### compiles return terminator to result assignment

1. make arg local
2. make return local
3. id: BlockId
4. terminator: MirTerminator Return
5. check msg
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_return_local(1, make_i32())
]

val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0)))))
)
val func = make_function("return_arg", [make_i32()], make_i32(), locals, [block])
val module = make_module("return_arg_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for return terminator")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("result_out <= a;"))
```

</details>

#### compiles if terminator return arms to result mux

1. make arg local
2. make arg local
3. make arg local
4. make return local
5. id: BlockId
6. MirOperand
7. BlockId
8. BlockId
9. id: BlockId
10. terminator: MirTerminator Return
11. id: BlockId
12. terminator: MirTerminator Return
13. check msg
14. check
15. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_resolved_backend()

val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_return_local(3, make_i32())
]

val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.If(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        BlockId(id: 1),
        BlockId(id: 2)
    )
)
val then_block = MirBlock(
    id: BlockId(id: 1),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))))
)
val else_block = MirBlock(
    id: BlockId(id: 2),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2)))))
)

val func = make_function("select_i32", [make_bool(), make_i32(), make_i32()], make_i32(), locals, [entry, then_block, else_block])
val module = make_module("select_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for if terminator")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("flag : in std_logic"))
check(vhdl.contains("result_out <= a when flag = '1' else b;"))
```

</details>

#### compiles branch-local computations inside combinational process

1. make arg local
2. make arg local
3. make arg local
4. make return local
5. make temp local
6. make temp local
7. id: BlockId
8. MirOperand
9. BlockId
10. BlockId
11. LocalId
12. MirOperand
13. MirOperand
14. span: empty span
15. id: BlockId
16. terminator: MirTerminator Return
17. LocalId
18. MirOperand
19. MirOperand
20. span: empty span
21. id: BlockId
22. terminator: MirTerminator Return
23. check msg
24. check
25. check
26. check
27. check
28. check
29. check
30. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_resolved_backend()

val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_return_local(3, make_i32()),
    make_temp_local(4, "then_tmp", make_i32()),
    make_temp_local(5, "else_tmp", make_i32())
]

val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.If(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        BlockId(id: 1),
        BlockId(id: 2)
    )
)
val then_add = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 4),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val then_block = MirBlock(
    id: BlockId(id: 1),
    instructions: [then_add],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4)))))
)
val else_sub = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 5),
        MirBinOp.Sub,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val else_block = MirBlock(
    id: BlockId(id: 2),
    instructions: [else_sub],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 5)))))
)

val func = make_function("select_computed_i32", [make_bool(), make_i32(), make_i32()], make_i32(), locals, [entry, then_block, else_block])
val module = make_module("select_computed_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for computed if terminator")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("comb: process(all)"))
check(vhdl.contains("variable v_then_tmp : signed(31 downto 0);"))
check(vhdl.contains("if flag = '1' then"))
check(vhdl.contains("v_then_tmp := a + to_signed(1, 32);"))
check(vhdl.contains("result_out <= v_then_tmp;"))
check(vhdl.contains("v_else_tmp := b - to_signed(1, 32);"))
check(vhdl.contains("result_out <= v_else_tmp;"))
```

</details>

#### compiles branch-local VHDL resize slice and concat inside combinational process

1. make arg local
2. make arg local
3. make arg local
4. make return local
5. make temp local
6. make temp local
7. make temp local
8. make temp local
9. id: BlockId
10. MirOperand
11. BlockId
12. BlockId
13. LocalId
14. MirOperand
15. span: empty span
16. id: BlockId
17. terminator: MirTerminator Return
18. LocalId
19. MirOperand
20. MirOperand
21. MirOperand
22. MirOperand
23. span: empty span
24. LocalId
25. MirOperand
26. span: empty span
27. LocalId
28. MirOperand
29. span: empty span
30. id: BlockId
31. terminator: MirTerminator Return
32. check msg
33. check
34. check
35. check
36. check
37. check
38. check
39. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 87 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_resolved_backend()
val u32 = MirType(kind: MirTypeKind.U32)

val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_arg_local(1, 1, "a", make_u8()),
    make_arg_local(2, 2, "b", make_u8()),
    make_return_local(3, u32),
    make_temp_local(4, "then_wide", u32),
    make_temp_local(5, "cat", u32),
    make_temp_local(6, "low", make_u8()),
    make_temp_local(7, "else_wide", u32)
]

val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.If(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        BlockId(id: 1),
        BlockId(id: 2)
    )
)
val then_resize = MirInst(
    kind: MirInstKind.VhdlResize(
        LocalId(id: 4),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
        32,
        false
    ),
    span: empty_span()
)
val then_block = MirBlock(
    id: BlockId(id: 1),
    instructions: [then_resize],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4)))))
)
val else_concat = MirInst(
    kind: MirInstKind.VhdlConcat(
        LocalId(id: 5),
        [
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2)))
        ]
    ),
    span: empty_span()
)
val else_slice = MirInst(
    kind: MirInstKind.VhdlSlice(
        LocalId(id: 6),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 5))),
        7,
        0
    ),
    span: empty_span()
)
val else_resize = MirInst(
    kind: MirInstKind.VhdlResize(
        LocalId(id: 7),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 6))),
        32,
        false
    ),
    span: empty_span()
)
val else_block = MirBlock(
    id: BlockId(id: 2),
    instructions: [else_concat, else_slice, else_resize],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 7)))))
)

val func = make_function("select_vhdl_width_ops", [make_bool(), make_u8(), make_u8()], u32, locals, [entry, then_block, else_block])
val module = make_module("select_vhdl_width_ops_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for process VHDL width ops")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("comb: process(all)"))
check(vhdl.contains("variable v_then_wide : unsigned(31 downto 0);"))
check(vhdl.contains("v_then_wide := resize(a, 32);"))
check(vhdl.contains("v_cat := b & b & b & b;"))
check(vhdl.contains("v_low := v_cat(7 downto 0);"))
check(vhdl.contains("v_else_wide := resize(v_low, 32);"))
check(vhdl.contains("result_out <= v_else_wide;"))
```

</details>

#### compiles branch-local VHDL signal and variable assignments inside combinational process

1. make arg local
2. make arg local
3. make arg local
4. make return local
5. make temp local
6. id: BlockId
7. MirOperand
8. BlockId
9. BlockId
10. MirOperand
11. MirOperand
12. span: empty span
13. id: BlockId
14. terminator: MirTerminator Return
15. MirOperand
16. MirOperand
17. span: empty span
18. id: BlockId
19. terminator: MirTerminator Return
20. check msg
21. check
22. check
23. check
24. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_resolved_backend()

val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_return_local(3, make_i32()),
    make_temp_local(4, "tmp", make_i32())
]

val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.If(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        BlockId(id: 1),
        BlockId(id: 2)
    )
)
val then_assign = MirInst(
    kind: MirInstKind.VhdlVarAssign(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4))),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))
    ),
    span: empty_span()
)
val then_block = MirBlock(
    id: BlockId(id: 1),
    instructions: [then_assign],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4)))))
)
val else_assign = MirInst(
    kind: MirInstKind.VhdlSignalAssign(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3))),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
        nil
    ),
    span: empty_span()
)
val else_block = MirBlock(
    id: BlockId(id: 2),
    instructions: [else_assign],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3)))))
)

val func = make_function("select_vhdl_assigns", [make_bool(), make_i32(), make_i32()], make_i32(), locals, [entry, then_block, else_block])
val module = make_module("select_vhdl_assigns_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for process VHDL assigns")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("comb: process(all)"))
check(vhdl.contains("v_tmp := a;"))
check(vhdl.contains("result_out <= v_tmp;"))
check(vhdl.contains("result_out <= b;"))
```

</details>

#### compiles checked binary op and integer casts

1. make arg local
2. make arg local
3. make return local
4. make temp local
5. make temp local
6. make temp local
7. LocalId
8. MirOperand
9. MirOperand
10. span: empty span
11. LocalId
12. MirOperand
13. MirType
14. span: empty span
15. LocalId
16. MirOperand
17. make i32
18. span: empty span
19. id: BlockId
20. terminator: MirTerminator Return
21. check msg
22. check
23. check
24. check
25. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_arg_local(1, 1, "b", make_i32()),
    make_return_local(2, make_i32()),
    make_temp_local(3, "sum", make_i32()),
    make_temp_local(4, "wide", MirType(kind: MirTypeKind.I64)),
    make_temp_local(5, "narrow", make_i32())
]

val checked_add = MirInst(
    kind: MirInstKind.CheckedBinOp(
        LocalId(id: 3),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))
    ),
    span: empty_span()
)
val widen = MirInst(
    kind: MirInstKind.Cast(
        LocalId(id: 4),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3))),
        MirType(kind: MirTypeKind.I64)
    ),
    span: empty_span()
)
val narrow = MirInst(
    kind: MirInstKind.Bitcast(
        LocalId(id: 5),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4))),
        make_i32()
    ),
    span: empty_span()
)

val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [checked_add, widen, narrow],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 5)))))
)
val func = make_function("cast_checked", [make_i32(), make_i32()], make_i32(), locals, [block])
val module = make_module("cast_checked_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for checked op/cast")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("sum <= a + b;"))
check(vhdl.contains("wide <= resize(signed(sum), 64);"))
check(vhdl.contains("narrow <= resize(signed(wide), 32);"))
check(vhdl.contains("result_out <= narrow;"))
```

</details>

#### compiles typed bool casts and shift counts

1. make arg local
2. make arg local
3. make arg local
4. make arg local
5. make return local
6. make temp local
7. make temp local
8. make temp local
9. make temp local
10. make temp local
11. LocalId
12. MirOperand
13. make bool
14. span: empty span
15. LocalId
16. MirOperand
17. span: empty span
18. LocalId
19. MirOperand
20. MirOperand
21. span: empty span
22. LocalId
23. MirOperand
24. MirOperand
25. span: empty span
26. LocalId
27. MirOperand
28. MirOperand
29. span: empty span
30. id: BlockId
31. terminator: MirTerminator Return
32. check msg
33. check
34. check
35. check
36. check
37. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 78 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val u32 = MirType(kind: MirTypeKind.U32)
val u8 = MirType(kind: MirTypeKind.U8)

val locals = [
    make_arg_local(0, 0, "data", u32),
    make_arg_local(1, 1, "shamt_u", u8),
    make_arg_local(2, 2, "shamt_s", make_i32()),
    make_arg_local(3, 3, "flag", make_bool()),
    make_return_local(4, u32),
    make_temp_local(5, "flag_from_data", make_bool()),
    make_temp_local(6, "count_from_flag", u8),
    make_temp_local(7, "shl_const", u32),
    make_temp_local(8, "shl_signal", u32),
    make_temp_local(9, "shr_signed", u32)
]

val int_to_bool = MirInst(
    kind: MirInstKind.Cast(
        LocalId(id: 5),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        make_bool()
    ),
    span: empty_span()
)
val bool_to_unsigned = MirInst(
    kind: MirInstKind.Cast(
        LocalId(id: 6),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3))),
        u8
    ),
    span: empty_span()
)
val shl_const = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 7),
        MirBinOp.Shl,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(3), u8))
    ),
    span: empty_span()
)
val shl_signal = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 8),
        MirBinOp.Shl,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))
    ),
    span: empty_span()
)
val shr_signed = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 9),
        MirBinOp.Shr,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2)))
    ),
    span: empty_span()
)

val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [int_to_bool, bool_to_unsigned, shl_const, shl_signal, shr_signed],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 9)))))
)
val func = make_function("typed_ops", [u32, u8, make_i32(), make_bool()], u32, locals, [block])
val module = make_module("typed_ops_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for typed casts/shifts")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("flag_from_data <= '1' when data /= to_unsigned(0, 32) else '0';"))
check(vhdl.contains("count_from_flag <= to_unsigned(1, 8) when flag = '1' else to_unsigned(0, 8);"))
check(vhdl.contains("shl_const <= shift_left(data, 3);"))
check(vhdl.contains("shl_signal <= shift_left(data, to_integer(shamt_u));"))
check(vhdl.contains("shr_signed <= shift_right(data, to_integer(unsigned(shamt_s)));"))
```

</details>

#### compiles remainder and bitwise not operations

1. make arg local
2. make arg local
3. make return local
4. make temp local
5. make temp local
6. LocalId
7. MirOperand
8. MirOperand
9. span: empty span
10. LocalId
11. MirOperand
12. span: empty span
13. id: BlockId
14. terminator: MirTerminator Return
15. check msg
16. check
17. check
18. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_arg_local(1, 1, "b", make_i32()),
    make_return_local(2, make_i32()),
    make_temp_local(3, "rem_value", make_i32()),
    make_temp_local(4, "inverted", make_i32())
]

val rem_inst = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 3),
        MirBinOp.Rem,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))
    ),
    span: empty_span()
)
val bitnot_inst = MirInst(
    kind: MirInstKind.UnaryOp(
        LocalId(id: 4),
        MirUnaryOp.BitNot,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3)))
    ),
    span: empty_span()
)
val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [rem_inst, bitnot_inst],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4)))))
)
val func = make_function("rem_not", [make_i32(), make_i32()], make_i32(), locals, [block])
val module = make_module("rem_not_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for rem/bitnot")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("rem_value <= a mod b;"))
check(vhdl.contains("inverted <= not rem_value;"))
check(vhdl.contains("result_out <= inverted;"))
```

</details>

#### compiles goto terminator to return block

1. make arg local
2. make return local
3. id: BlockId
4. terminator: MirTerminator Goto
5. id: BlockId
6. terminator: MirTerminator Return
7. check msg
8. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_return_local(1, make_i32())
]

val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.Goto(BlockId(id: 1))
)
val ret = MirBlock(
    id: BlockId(id: 1),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0)))))
)
val func = make_function("goto_return", [make_i32()], make_i32(), locals, [entry, ret])
val module = make_module("goto_return_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for goto return")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("result_out <= a;"))
```

</details>

#### compiles goto chains and if arms that jump to returns

1. make arg local
2. make arg local
3. make arg local
4. make return local
5. id: BlockId
6. MirOperand
7. BlockId
8. BlockId
9. id: BlockId
10. terminator: MirTerminator Return
11. id: BlockId
12. terminator: MirTerminator Return
13. check msg
14. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_return_local(3, make_i32())
]
val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.If(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        BlockId(id: 1),
        BlockId(id: 2)
    )
)
val then_jump = MirBlock(id: BlockId(id: 1), instructions: [], terminator: MirTerminator.Goto(BlockId(id: 3)))
val else_jump = MirBlock(id: BlockId(id: 2), instructions: [], terminator: MirTerminator.Goto(BlockId(id: 4)))
val then_ret = MirBlock(
    id: BlockId(id: 3),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))))
)
val else_ret = MirBlock(
    id: BlockId(id: 4),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2)))))
)

val func = make_function("select_jump", [make_bool(), make_i32(), make_i32()], make_i32(), locals, [entry, then_jump, else_jump, then_ret, else_ret])
val module = make_module("select_jump_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for if/goto return chain")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("result_out <= a when flag = '1' else b;"))
```

</details>

#### compiles switch terminator return targets to conditional result

1. make arg local
2. make arg local
3. make arg local
4. make arg local
5. make return local
6. id: BlockId
7. MirOperand
8. SwitchCase
9. SwitchCase
10. BlockId
11. id: BlockId
12. terminator: MirTerminator Return
13. id: BlockId
14. terminator: MirTerminator Return
15. id: BlockId
16. terminator: MirTerminator Return
17. check msg
18. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val u8 = MirType(kind: MirTypeKind.U8)
val locals = [
    make_arg_local(0, 0, "sel", u8),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_arg_local(3, 3, "c", make_i32()),
    make_return_local(4, make_i32())
]
val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.Switch(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        [
            SwitchCase(value: 0, target: BlockId(id: 1)),
            SwitchCase(value: 1, target: BlockId(id: 2))
        ],
        BlockId(id: 3)
    )
)
val case_zero = MirBlock(
    id: BlockId(id: 1),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))))
)
val case_one = MirBlock(
    id: BlockId(id: 2),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2)))))
)
val default_case = MirBlock(
    id: BlockId(id: 3),
    instructions: [],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3)))))
)
val func = make_function("select_switch", [u8, make_i32(), make_i32(), make_i32()], make_i32(), locals, [entry, case_zero, case_one, default_case])
val module = make_module("switch_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for switch terminator")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("result_out <= a when sel = to_unsigned(0, 8) else b when sel = to_unsigned(1, 8) else c;"))
```

</details>

#### compiles switch targets with computations inside combinational process

1. make arg local
2. make arg local
3. make arg local
4. make arg local
5. make return local
6. make temp local
7. make temp local
8. make temp local
9. id: BlockId
10. MirOperand
11. SwitchCase
12. SwitchCase
13. BlockId
14. LocalId
15. MirOperand
16. MirOperand
17. span: empty span
18. id: BlockId
19. terminator: MirTerminator Return
20. LocalId
21. MirOperand
22. MirOperand
23. span: empty span
24. id: BlockId
25. terminator: MirTerminator Return
26. LocalId
27. MirOperand
28. MirOperand
29. span: empty span
30. id: BlockId
31. terminator: MirTerminator Return
32. check msg
33. check
34. check
35. check
36. check
37. check
38. check
39. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_resolved_backend()
val u8 = make_u8()
val locals = [
    make_arg_local(0, 0, "sel", u8),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_arg_local(3, 3, "c", make_i32()),
    make_return_local(4, make_i32()),
    make_temp_local(5, "case_zero_tmp", make_i32()),
    make_temp_local(6, "case_one_tmp", make_i32()),
    make_temp_local(7, "default_tmp", make_i32())
]
val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.Switch(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        [
            SwitchCase(value: 0, target: BlockId(id: 1)),
            SwitchCase(value: 1, target: BlockId(id: 2))
        ],
        BlockId(id: 3)
    )
)
val case_zero_add = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 5),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val case_zero = MirBlock(
    id: BlockId(id: 1),
    instructions: [case_zero_add],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 5)))))
)
val case_one_sub = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 6),
        MirBinOp.Sub,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val case_one = MirBlock(
    id: BlockId(id: 2),
    instructions: [case_one_sub],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 6)))))
)
val default_add = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 7),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(2), make_i32()))
    ),
    span: empty_span()
)
val default_case = MirBlock(
    id: BlockId(id: 3),
    instructions: [default_add],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 7)))))
)
val func = make_function("select_switch_computed", [u8, make_i32(), make_i32(), make_i32()], make_i32(), locals, [entry, case_zero, case_one, default_case])
val module = make_module("switch_computed_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for computed switch terminator")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("comb: process(all)"))
check(vhdl.contains("if sel = to_unsigned(0, 8) then"))
check(vhdl.contains("elsif sel = to_unsigned(1, 8) then"))
check(vhdl.contains("v_case_zero_tmp := a + to_signed(1, 32);"))
check(vhdl.contains("v_case_one_tmp := b - to_signed(1, 32);"))
check(vhdl.contains("v_default_tmp := c + to_signed(2, 32);"))
check(vhdl.contains("result_out <= v_default_tmp;"))
```

</details>

#### compiles struct aggregate to named record assignment

1. make field
2. make field
3. types[point symbol] = make type def
4. make arg local
5. make arg local
6. make return local
7. make temp local
8. LocalId
9. AggregateKind Struct
10. MirOperand
11. MirOperand
12. span: empty span
13. id: BlockId
14. terminator: MirTerminator Return
15. check msg
16. check
17. check
18. check
19. check
20. check
21. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val point_symbol = SymbolId(id: 42)
val point_type = MirType(kind: MirTypeKind.Struct(point_symbol))
val fields = [
    make_field("x", make_i32()),
    make_field("y", make_i32())
]
var types: Dict<SymbolId, MirTypeDef> = {}
types[point_symbol] = make_type_def(point_symbol, "Point", MirTypeDefKind.Struct(fields))

val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_arg_local(1, 1, "b", make_i32()),
    make_return_local(2, point_type),
    make_temp_local(3, "point_sig", point_type)
]
val aggregate = MirInst(
    kind: MirInstKind.Aggregate(
        LocalId(id: 3),
        AggregateKind.Struct(point_symbol),
        [
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))
        ]
    ),
    span: empty_span()
)
val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [aggregate],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3)))))
)
val func = make_function("make_point", [make_i32(), make_i32()], point_type, locals, [block])
var functions: Dict<SymbolId, MirFunction> = {}
functions[func.symbol] = func
val module = MirModule(name: "point_mod", functions: functions, statics: {}, constants: {}, types: types)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for struct aggregate")

val compiled = result.unwrap()
check(compiled.package_vhdl.?)
check(compiled.package_vhdl.unwrap().contains("type Point is record"))
val vhdl = compiled.vhdl
check(vhdl.contains("result_out : out Point"))
check(vhdl.contains("signal point_sig : Point;"))
check(vhdl.contains("point_sig <= (x => a, y => b);"))
check(vhdl.contains("result_out <= point_sig;"))
```

</details>

#### compiles branch-local struct aggregates inside combinational process

1. make field
2. make field
3. types[point symbol] = make type def
4. make arg local
5. make arg local
6. make arg local
7. make return local
8. make temp local
9. make temp local
10. id: BlockId
11. MirOperand
12. BlockId
13. BlockId
14. LocalId
15. AggregateKind Struct
16. MirOperand
17. MirOperand
18. span: empty span
19. id: BlockId
20. terminator: MirTerminator Return
21. LocalId
22. AggregateKind Struct
23. MirOperand
24. MirOperand
25. span: empty span
26. id: BlockId
27. terminator: MirTerminator Return
28. check msg
29. check
30. check
31. check
32. check
33. check
34. check
35. check
36. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 78 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_resolved_backend()
val point_symbol = SymbolId(id: 44)
val point_type = MirType(kind: MirTypeKind.Struct(point_symbol))
val fields = [
    make_field("x", make_i32()),
    make_field("y", make_i32())
]
var types: Dict<SymbolId, MirTypeDef> = {}
types[point_symbol] = make_type_def(point_symbol, "BranchPoint", MirTypeDefKind.Struct(fields))

val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_return_local(3, point_type),
    make_temp_local(4, "then_point", point_type),
    make_temp_local(5, "else_point", point_type)
]
val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.If(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        BlockId(id: 1),
        BlockId(id: 2)
    )
)
val then_aggregate = MirInst(
    kind: MirInstKind.Aggregate(
        LocalId(id: 4),
        AggregateKind.Struct(point_symbol),
        [
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2)))
        ]
    ),
    span: empty_span()
)
val then_block = MirBlock(
    id: BlockId(id: 1),
    instructions: [then_aggregate],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4)))))
)
val else_aggregate = MirInst(
    kind: MirInstKind.Aggregate(
        LocalId(id: 5),
        AggregateKind.Struct(point_symbol),
        [
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))
        ]
    ),
    span: empty_span()
)
val else_block = MirBlock(
    id: BlockId(id: 2),
    instructions: [else_aggregate],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 5)))))
)

val func = make_function("select_point", [make_bool(), make_i32(), make_i32()], point_type, locals, [entry, then_block, else_block])
var functions: Dict<SymbolId, MirFunction> = {}
functions[func.symbol] = func
val module = MirModule(name: "branch_point_mod", functions: functions, statics: {}, constants: {}, types: types)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for branch-local struct aggregate")

val compiled = result.unwrap()
check(compiled.package_vhdl.?)
check(compiled.package_vhdl.unwrap().contains("type BranchPoint is record"))
val vhdl = compiled.vhdl
check(vhdl.contains("comb: process(all)"))
check(vhdl.contains("variable v_then_point : BranchPoint;"))
check(vhdl.contains("v_then_point := (x => a, y => b);"))
check(vhdl.contains("result_out <= v_then_point;"))
check(vhdl.contains("v_else_point := (x => b, y => a);"))
check(vhdl.contains("result_out <= v_else_point;"))
```

</details>

#### compiles struct field get and set

1. make field
2. make field
3. types[point symbol] = make type def
4. make arg local
5. make return local
6. make temp local
7. make temp local
8. MirOperand
9. MirOperand
10. span: empty span
11. LocalId
12. MirOperand
13. span: empty span
14. id: BlockId
15. terminator: MirTerminator Return
16. check msg
17. check
18. check
19. check
20. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val point_symbol = SymbolId(id: 43)
val point_type = MirType(kind: MirTypeKind.Struct(point_symbol))
val fields = [
    make_field("x", make_i32()),
    make_field("y", make_i32())
]
var types: Dict<SymbolId, MirTypeDef> = {}
types[point_symbol] = make_type_def(point_symbol, "Point2", MirTypeDefKind.Struct(fields))

val locals = [
    make_arg_local(0, 0, "new_y", make_i32()),
    make_return_local(1, make_i32()),
    make_temp_local(2, "point_sig", point_type),
    make_temp_local(3, "x_out", make_i32())
]
val set_y = MirInst(
    kind: MirInstKind.SetField(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
        1,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0)))
    ),
    span: empty_span()
)
val get_x = MirInst(
    kind: MirInstKind.GetField(
        LocalId(id: 3),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
        0
    ),
    span: empty_span()
)
val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [set_y, get_x],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3)))))
)
val func = make_function("point_fields", [make_i32()], make_i32(), locals, [block])
var functions: Dict<SymbolId, MirFunction> = {}
functions[func.symbol] = func
val module = MirModule(name: "point_fields_mod", functions: functions, statics: {}, constants: {}, types: types)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for struct fields")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("signal point_sig : Point2;"))
check(vhdl.contains("point_sig.y <= new_y;"))
check(vhdl.contains("x_out <= point_sig.x;"))
check(vhdl.contains("result_out <= x_out;"))
```

</details>

#### compiles array aggregate assignment

1. make arg local
2. make arg local
3. make temp local
4. LocalId
5. AggregateKind Array
6. MirOperand
7. MirOperand
8. span: empty span
9. id: BlockId
10. check msg
11. check
12. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val array_type = MirType(kind: MirTypeKind.Array(make_i32(), 2))
val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_arg_local(1, 1, "b", make_i32()),
    make_temp_local(2, "arr_sig", array_type)
]
val aggregate = MirInst(
    kind: MirInstKind.Aggregate(
        LocalId(id: 2),
        AggregateKind.Array(make_i32()),
        [
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
            MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))
        ]
    ),
    span: empty_span()
)
val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [aggregate],
    terminator: nil
)
val func = make_function("make_pair_array", [make_i32(), make_i32()], make_type(MirTypeKind.Unit), locals, [block])
val module = make_module("array_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for array aggregate")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("signal arr_sig : array (0 to 1) of signed(31 downto 0);"))
check(vhdl.contains("arr_sig <= (0 => a, 1 => b);"))
```

</details>

#### compiles explicit VHDL port map component instantiation

1. make arg local
2. make arg local
3. make return local
4. make temp local
5.
6.
7.
8. span: empty span
9. id: BlockId
10. terminator: MirTerminator Return
11. check msg
12. check
13. check
14. check
15. check
16. check
17. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val locals = [
    make_arg_local(0, 0, "lhs", make_i32()),
    make_arg_local(1, 1, "rhs", make_i32()),
    make_return_local(2, make_i32()),
    make_temp_local(3, "sum_sig", make_i32())
]
val port_map = MirInst(
    kind: MirInstKind.VhdlPortMap(
        "adder",
        "u_add",
        [
            ("a", MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0)))),
            ("b", MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))),
            ("result_out", MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3))))
        ]
    ),
    span: empty_span()
)
val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [port_map],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3)))))
)
val func = make_function("uses_adder", [make_i32(), make_i32()], make_i32(), locals, [block])
val module = make_module("port_map_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for VHDL port map")

val vhdl = result.unwrap().vhdl
check(vhdl.contains("u_add: entity work.adder"))
check(vhdl.contains("port map ("))
check(vhdl.contains("a => lhs,"))
check(vhdl.contains("b => rhs,"))
check(vhdl.contains("result_out => sum_sig"))
check(vhdl.contains("result_out <= sum_sig;"))
```

</details>

#### rejects unsupported MIR instruction with hard error

1. make arg local
2. make return local
3. Some
4. MirOperand
5. [MirOperand
6. span: empty span
7. id: BlockId
8. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

# Use a Call instruction which is unsupported in VHDL
val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_return_local(1, make_i32())
]

val call_inst = MirInst(
    kind: MirInstKind.Call(
        Some(LocalId(id: 1)),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Str("missing_helper"), MirType(kind: MirTypeKind.Opaque(name: "fnptr")))),
        [MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0)))]
    ),
    span: empty_span()
)

val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [call_inst],
    terminator: nil
)

val func = make_function("bad_func", [make_i32()], make_i32(), locals, [block])
val module = make_module("bad_module", func)

val result = backend.compile(module)
check_msg(result.is_err(), "Expected hard error for unsupported Call instruction")
```

</details>

#### rejects storage allocation as unsupported synthesizable VHDL

1. make return local
2. make temp local
3. kind: MirInstKind Alloc
4. span: empty span
5. id: BlockId
6. terminator: MirTerminator Return
7. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val ptr_type = MirType(kind: MirTypeKind.Ptr(make_i32(), true))
val locals = [
    make_return_local(0, make_i32()),
    make_temp_local(1, "ptr", ptr_type)
]
val alloc_inst = MirInst(
    kind: MirInstKind.Alloc(LocalId(id: 1), make_i32()),
    span: empty_span()
)
val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [alloc_inst],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0), make_i32()))))
)
val func = make_function("bad_alloc", [], make_i32(), locals, [block])
val module = make_module("bad_alloc_mod", func)

val result = backend.compile(module)
check_msg(result.is_err(), "Expected hard error for unsupported Alloc instruction")
```

</details>

#### rejects pointer address arithmetic as unsupported synthesizable VHDL

1. make arg local
2. make return local
3. make temp local
4. LocalId
5. MirOperand
6. [MirOperand
7. span: empty span
8. id: BlockId
9. terminator: MirTerminator Return
10. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val ptr_type = MirType(kind: MirTypeKind.Ptr(make_i32(), true))
val locals = [
    make_arg_local(0, 0, "ptr", ptr_type),
    make_return_local(1, make_i32()),
    make_temp_local(2, "next_ptr", ptr_type)
]
val gep_inst = MirInst(
    kind: MirInstKind.GetElementPtr(
        LocalId(id: 2),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        [MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))]
    ),
    span: empty_span()
)
val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [gep_inst],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(0), make_i32()))))
)
val func = make_function("bad_gep", [ptr_type], make_i32(), locals, [block])
val module = make_module("bad_gep_mod", func)

val result = backend.compile(module)
check_msg(result.is_err(), "Expected hard error for unsupported GetElementPtr instruction")
```

</details>

#### rejects indirect calls as unsupported synthesizable VHDL

1. make arg local
2. make arg local
3. make return local
4. Some
5. MirOperand
6. [MirOperand
7. MirSignature
8. span: empty span
9. id: BlockId
10. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val ptr_type = MirType(kind: MirTypeKind.Ptr(make_i32(), false))
val locals = [
    make_arg_local(0, 0, "fn_ptr", ptr_type),
    make_arg_local(1, 1, "a", make_i32()),
    make_return_local(2, make_i32())
]
val call_inst = MirInst(
    kind: MirInstKind.CallIndirect(
        Some(LocalId(id: 2)),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        [MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1)))],
        MirSignature(params: [make_i32()], return_type: make_i32(), is_variadic: false)
    ),
    span: empty_span()
)
val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [call_inst],
    terminator: nil
)
val func = make_function("bad_call_indirect", [ptr_type, make_i32()], make_i32(), locals, [block])
val module = make_module("bad_call_indirect_mod", func)

val result = backend.compile(module)
check_msg(result.is_err(), "Expected hard error for unsupported CallIndirect instruction")
```

</details>

#### rejects arbitrary intrinsics as unsupported synthesizable VHDL

1. make arg local
2. make return local
3. Some
4. [MirOperand
5. span: empty span
6. id: BlockId
7. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_return_local(1, make_i32())
]
val intrinsic_inst = MirInst(
    kind: MirInstKind.Intrinsic(
        Some(LocalId(id: 1)),
        "host_only",
        [MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0)))]
    ),
    span: empty_span()
)
val block = MirBlock(
    id: BlockId(id: 0),
    instructions: [intrinsic_inst],
    terminator: nil
)
val func = make_function("bad_intrinsic", [make_i32()], make_i32(), locals, [block])
val module = make_module("bad_intrinsic_mod", func)

val result = backend.compile(module)
check_msg(result.is_err(), "Expected hard error for unsupported Intrinsic instruction")
```

</details>

#### rejects delayed signal assignment inside structured process

1. make arg local
2. make arg local
3. make arg local
4. make return local
5. make temp local
6. id: BlockId
7. MirOperand
8. BlockId
9. BlockId
10. LocalId
11. MirOperand
12. MirOperand
13. span: empty span
14. id: BlockId
15. terminator: MirTerminator Return
16. MirOperand
17. MirOperand
18. Some
19. span: empty span
20. id: BlockId
21. terminator: MirTerminator Return
22. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_resolved_backend()
val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_return_local(3, make_i32()),
    make_temp_local(4, "tmp", make_i32())
]
val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.If(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        BlockId(id: 1),
        BlockId(id: 2)
    )
)
val then_add = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 4),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val then_block = MirBlock(
    id: BlockId(id: 1),
    instructions: [then_add],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4)))))
)
val delayed_assign = MirInst(
    kind: MirInstKind.VhdlSignalAssign(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3))),
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
        Some(10)
    ),
    span: empty_span()
)
val else_block = MirBlock(
    id: BlockId(id: 2),
    instructions: [delayed_assign],
    terminator: MirTerminator.Return(nil)
)
val func = make_function("bad_delayed_process_assign", [make_bool(), make_i32(), make_i32()], make_i32(), locals, [entry, then_block, else_block])
val module = make_module("bad_delayed_process_assign_mod", func)

val result = backend.compile(module)
check_msg(result.is_err(), "Expected hard error for delayed signal assignment inside process")
```

</details>

### VHDL Backend E2E - Package Generation

#### compiles struct type to VHDL record package

1. make field
2. make field
3. types[point symbol] = make type def
4. check msg
5. check
6. check
7. check
8. check
9. check
10. check
11. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

val struct_fields = [
    make_field("x", make_i32()),
    make_field("y", make_i32())
]

var types: Dict<SymbolId, MirTypeDef> = {}
val point_symbol = SymbolId(id: 0)
types[point_symbol] = make_type_def(point_symbol, "Point", MirTypeDefKind.Struct(struct_fields))

val module = MirModule(
    name: "geom",
    functions: {},
    statics: {},
    constants: {},
    types: types
)

val result = backend.compile(module)
check_msg(result.is_ok(), "Package compilation failed")

val compiled = result.unwrap()
check(compiled.package_vhdl.?)
val pkg = compiled.package_vhdl.unwrap()
check(pkg.contains("package geom_pkg is"))
check(pkg.contains("type Point is record"))
check(pkg.contains("x : signed(31 downto 0);"))
check(pkg.contains("y : signed(31 downto 0);"))
check(pkg.contains("end record"))
check(pkg.contains("end package geom_pkg;"))
```

</details>

#### compiles enum type to VHDL enumeration

1. make variant
2. make variant
3. make variant
4. types[state symbol] = make type def
5. check msg
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()

val variants = [
    make_variant("Idle", 0),
    make_variant("Running", 1),
    make_variant("Done", 2)
]

var types: Dict<SymbolId, MirTypeDef> = {}
val state_symbol = SymbolId(id: 0)
types[state_symbol] = make_type_def(state_symbol, "State", MirTypeDefKind.Enum(variants))

val module = MirModule(
    name: "fsm",
    functions: {},
    statics: {},
    constants: {},
    types: types
)

val result = backend.compile(module)
check_msg(result.is_ok(), "Enum package compilation failed")

val compiled = result.unwrap()
check(compiled.package_vhdl.?)
val pkg = compiled.package_vhdl.unwrap()
check(pkg.contains("type State is (Idle, Running, Done);"))
```

</details>

### VHDL Backend E2E - GHDL Validation

<details>
<summary>Advanced: backend-generated adder passes GHDL analysis</summary>

#### backend-generated adder passes GHDL analysis _(slow)_

1. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: GHDL not available"
    return

val valid = write_and_analyze(compile_add_vhdl(), "adder")
check_msg(valid, "GHDL rejected backend-generated add VHDL")
```

</details>


</details>

<details>
<summary>Advanced: backend-generated add passes GHDL elaboration and synthesis</summary>

#### backend-generated add passes GHDL elaboration and synthesis _(slow)_

1. check
2. check msg
3. check msg
4. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: GHDL not available"
    return

val add_vhdl = compile_add_vhdl()
val path = "/tmp/simple_vhdl_e2e_add_roundtrip.vhd"
check(vhdl_write_file(path, add_vhdl))

val analyze = ghdl_analyze(path)
check_msg(analyze.success, "GHDL analysis failed for generated add VHDL")

val elaborate = ghdl_elaborate("add")
check_msg(elaborate.success, "GHDL elaboration failed for generated add entity")

val synth = ghdl_synth("add")
check_msg(synth.success, "GHDL synthesis failed for generated add entity")
```

</details>


</details>

<details>
<summary>Advanced: backend-generated add testbench simulates 2 plus 3 equals 5</summary>

#### backend-generated add testbench simulates 2 plus 3 equals 5 _(slow)_

1. check
2. check msg
3. check
4. check msg
5. check msg
6. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: GHDL not available"
    return

val add_vhdl = compile_add_vhdl()
val add_path = "/tmp/simple_vhdl_e2e_add_tb_dut.vhd"
check(vhdl_write_file(add_path, add_vhdl))
val add_analyze = ghdl_analyze(add_path)
check_msg(add_analyze.success, "GHDL analysis failed for generated add DUT")

val tb_path = "/tmp/simple_vhdl_e2e_add_tb.vhd"
val tb_vhdl = make_add_testbench()
check(vhdl_write_file(tb_path, tb_vhdl))
val tb_analyze = ghdl_analyze(tb_path)
check_msg(tb_analyze.success, "GHDL analysis failed for generated add testbench")

val elaborate = ghdl_elaborate("add_tb")
check_msg(elaborate.success, "GHDL elaboration failed for generated add testbench")

val run_result = ghdl_run("add_tb", Some("10ns"))
check_msg(run_result.success, "GHDL simulation failed for generated add testbench")
```

</details>


</details>

<details>
<summary>Advanced: backend-generated package passes GHDL analysis</summary>

#### backend-generated package passes GHDL analysis _(slow)_

1. make field
2. make field
3. types[point symbol] = make type def
4. check msg
5. check
6. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: GHDL not available"
    return

val backend = make_backend()
val struct_fields = [
    make_field("x", make_i32()),
    make_field("y", make_i32())
]

var types: Dict<SymbolId, MirTypeDef> = {}
val point_symbol = SymbolId(id: 0)
types[point_symbol] = make_type_def(point_symbol, "Point", MirTypeDefKind.Struct(struct_fields))

val module = MirModule(name: "geom", functions: {}, statics: {}, constants: {}, types: types)

val result = backend.compile(module)
check_msg(result.is_ok(), "Package compilation failed")

val compiled = result.unwrap()
check(compiled.package_vhdl.?)
val pkg_valid = write_and_analyze(compiled.package_vhdl.unwrap(), "geom_pkg")
check_msg(pkg_valid, "GHDL rejected backend-generated package VHDL")
```

</details>


</details>

<details>
<summary>Advanced: backend-generated entity with package elaborates</summary>

#### backend-generated entity with package elaborates _(slow)_

1. make arg local
2. make return local
3. kind: MirInstKind Copy
4. span: empty span
5. check msg
6. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: GHDL not available"
    return

val backend = make_resolved_backend()
val locals = [
    make_arg_local(0, 0, "a", make_i32()),
    make_return_local(1, make_i32())
]

val nop_inst = MirInst(kind: MirInstKind.Nop, span: empty_span())
val copy_inst = MirInst(
    kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 0)),
    span: empty_span()
)

val block = MirBlock(id: BlockId(id: 0), instructions: [nop_inst, copy_inst], terminator: nil)
val func = make_function("passthrough", [make_i32()], make_i32(), locals, [block])
val module = make_module("pass_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for passthrough")

val compiled = result.unwrap()
val valid = write_and_analyze(compiled.vhdl, "passthrough")
check_msg(valid, "GHDL rejected backend-generated passthrough VHDL")
```

</details>


</details>

<details>
<summary>Advanced: backend-generated computed if process passes GHDL analysis and elaboration</summary>

#### backend-generated computed if process passes GHDL analysis and elaboration _(slow)_

1. make arg local
2. make arg local
3. make arg local
4. make return local
5. make temp local
6. make temp local
7. id: BlockId
8. MirOperand
9. BlockId
10. BlockId
11. LocalId
12. MirOperand
13. MirOperand
14. span: empty span
15. id: BlockId
16. terminator: MirTerminator Return
17. LocalId
18. MirOperand
19. MirOperand
20. span: empty span
21. id: BlockId
22. terminator: MirTerminator Return
23. check msg
24. check
25. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: GHDL not available"
    return

val backend = make_resolved_backend()
val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_return_local(3, make_i32()),
    make_temp_local(4, "then_tmp", make_i32()),
    make_temp_local(5, "else_tmp", make_i32())
]

val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.If(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        BlockId(id: 1),
        BlockId(id: 2)
    )
)
val then_add = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 4),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val then_block = MirBlock(
    id: BlockId(id: 1),
    instructions: [then_add],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 4)))))
)
val else_sub = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 5),
        MirBinOp.Sub,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val else_block = MirBlock(
    id: BlockId(id: 2),
    instructions: [else_sub],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 5)))))
)

val func = make_function("select_computed_i32", [make_bool(), make_i32(), make_i32()], make_i32(), locals, [entry, then_block, else_block])
val module = make_module("select_computed_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for computed if process")

val path = "/tmp/simple_vhdl_e2e_select_computed_i32.vhd"
check(vhdl_write_file(path, result.unwrap().vhdl))
val valid = ghdl_analyze_and_elaborate(path, "select_computed_i32")
check_msg(valid.success, "GHDL rejected backend-generated computed if process VHDL")
```

</details>


</details>

<details>
<summary>Advanced: backend-generated switch process passes GHDL analysis and elaboration</summary>

#### backend-generated switch process passes GHDL analysis and elaboration _(slow)_

1. make arg local
2. make arg local
3. make arg local
4. make arg local
5. make return local
6. make temp local
7. make temp local
8. make temp local
9. id: BlockId
10. MirOperand
11. SwitchCase
12. SwitchCase
13. BlockId
14. LocalId
15. MirOperand
16. MirOperand
17. span: empty span
18. id: BlockId
19. terminator: MirTerminator Return
20. LocalId
21. MirOperand
22. MirOperand
23. span: empty span
24. id: BlockId
25. terminator: MirTerminator Return
26. LocalId
27. MirOperand
28. MirOperand
29. span: empty span
30. id: BlockId
31. terminator: MirTerminator Return
32. check msg
33. check
34. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 80 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: GHDL not available"
    return

val backend = make_resolved_backend()
val u8 = make_u8()
val locals = [
    make_arg_local(0, 0, "sel", u8),
    make_arg_local(1, 1, "a", make_i32()),
    make_arg_local(2, 2, "b", make_i32()),
    make_arg_local(3, 3, "c", make_i32()),
    make_return_local(4, make_i32()),
    make_temp_local(5, "case_zero_tmp", make_i32()),
    make_temp_local(6, "case_one_tmp", make_i32()),
    make_temp_local(7, "default_tmp", make_i32())
]
val entry = MirBlock(
    id: BlockId(id: 0),
    instructions: [],
    terminator: MirTerminator.Switch(
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 0))),
        [
            SwitchCase(value: 0, target: BlockId(id: 1)),
            SwitchCase(value: 1, target: BlockId(id: 2))
        ],
        BlockId(id: 3)
    )
)
val case_zero_add = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 5),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 1))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val case_zero = MirBlock(
    id: BlockId(id: 1),
    instructions: [case_zero_add],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 5)))))
)
val case_one_sub = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 6),
        MirBinOp.Sub,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 2))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(1), make_i32()))
    ),
    span: empty_span()
)
val case_one = MirBlock(
    id: BlockId(id: 2),
    instructions: [case_one_sub],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 6)))))
)
val default_add = MirInst(
    kind: MirInstKind.BinOp(
        LocalId(id: 7),
        MirBinOp.Add,
        MirOperand(kind: MirOperandKind.Copy(LocalId(id: 3))),
        MirOperand(kind: MirOperandKind.Const(MirConstValue.Int(2), make_i32()))
    ),
    span: empty_span()
)
val default_case = MirBlock(
    id: BlockId(id: 3),
    instructions: [default_add],
    terminator: MirTerminator.Return(Some(MirOperand(kind: MirOperandKind.Copy(LocalId(id: 7)))))
)
val func = make_function("select_switch_computed", [u8, make_i32(), make_i32(), make_i32()], make_i32(), locals, [entry, case_zero, case_one, default_case])
val module = make_module("switch_computed_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Backend compilation failed for computed switch process")

val path = "/tmp/simple_vhdl_e2e_select_switch_computed.vhd"
check(vhdl_write_file(path, result.unwrap().vhdl))
val valid = ghdl_analyze_and_elaborate(path, "select_switch_computed")
check_msg(valid.success, "GHDL rejected backend-generated switch process VHDL")
```

</details>


</details>

<details>
<summary>Advanced: GHDL rejects intentionally invalid VHDL</summary>

#### GHDL rejects intentionally invalid VHDL _(slow)_

1. check
2. check msg
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not ghdl_available():
    print "SKIP: GHDL not available"
    return

val invalid_vhdl = "this is not valid VHDL at all;"
val path = "/tmp/simple_vhdl_e2e_negative.vhd"
check(vhdl_write_file(path, invalid_vhdl))
val result = ghdl_analyze(path)
check_msg(not result.success, "GHDL should reject invalid VHDL")
check(result.exit_code != 0)
```

</details>


</details>

### VHDL Backend E2E - Error Handling

#### rejects float type with clear error

1. make arg local
2. make return local
3. kind: MirInstKind Copy
4. span: empty span
5. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val locals = [
    make_arg_local(0, 0, "x", MirType(kind: MirTypeKind.F64)),
    make_return_local(1, MirType(kind: MirTypeKind.F64))
]

val copy_inst = MirInst(
    kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 0)),
    span: empty_span()
)

val block = MirBlock(id: BlockId(id: 0), instructions: [copy_inst], terminator: nil)
val func = make_function("bad_float", [MirType(kind: MirTypeKind.F64)], MirType(kind: MirTypeKind.F64), locals, [block])
val module = make_module("float_mod", func)

val result = backend.compile(module)
check_msg(result.is_err(), "Expected error for f64 type in VHDL backend")
```

</details>

#### rejects float constant with clear error

1. make return local
2. make temp local
3. LocalId
4. MirConstValue Float
5. MirType
6. span: empty span
7. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val locals = [
    make_return_local(0, make_i32()),
    make_temp_local(1, "bad", make_i32())
]

val float_const = MirInst(
    kind: MirInstKind.Const(
        LocalId(id: 1),
        MirConstValue.Float(3.14),
        MirType(kind: MirTypeKind.F64)
    ),
    span: empty_span()
)

val block = MirBlock(id: BlockId(id: 0), instructions: [float_const], terminator: nil)
val func = make_function("bad_const", [], make_i32(), locals, [block])
val module = make_module("const_mod", func)

val result = backend.compile(module)
check_msg(result.is_err(), "Expected error for float constant in VHDL backend")
```

</details>

#### Codegen trait returns Vhdl backend kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
expect(backend.backend_kind()).to_equal(BackendKind.Vhdl)
expect(backend.backend_name()).to_equal("vhdl")
```

</details>

### VHDL Backend E2E - Resolved Types

#### uses bit for unresolved backend

1. make arg local
2. make return local
3. check msg
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_backend()
val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_return_local(1, make_bool())
]
val copy = MirInst(kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 0)), span: empty_span())
val block = MirBlock(id: BlockId(id: 0), instructions: [copy], terminator: nil)
val func = make_function("id_bool", [make_bool()], make_bool(), locals, [block])
val module = make_module("bool_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Unresolved bool compilation failed")
check(result.unwrap().vhdl.contains("bit"))
```

</details>

#### uses std_logic for resolved backend

1. make arg local
2. make return local
3. check msg
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = make_resolved_backend()
val locals = [
    make_arg_local(0, 0, "flag", make_bool()),
    make_return_local(1, make_bool())
]
val copy = MirInst(kind: MirInstKind.Copy(LocalId(id: 1), LocalId(id: 0)), span: empty_span())
val block = MirBlock(id: BlockId(id: 0), instructions: [copy], terminator: nil)
val func = make_function("id_bool_resolved", [make_bool()], make_bool(), locals, [block])
val module = make_module("bool_resolved_mod", func)

val result = backend.compile(module)
check_msg(result.is_ok(), "Resolved bool compilation failed")
check(result.unwrap().vhdl.contains("std_logic"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
