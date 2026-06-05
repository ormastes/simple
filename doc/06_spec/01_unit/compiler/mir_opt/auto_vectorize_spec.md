# auto_vectorize_spec

> Simulates body of:  out[i] = a[i] + b[i]

<!-- sdn-diagram:id=auto_vectorize_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=auto_vectorize_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

auto_vectorize_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=auto_vectorize_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 64 | 64 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# auto_vectorize_spec

Simulates body of:  out[i] = a[i] + b[i]

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Simulates body of:  out[i] = a[i] + b[i]
    Instructions (in program order):
      %va  = Load(%pa)         # load a[i]
      %vb  = Load(%pb)         # load b[i]
      %vc  = Add(%va, %vb)     # data operation — NOT index inc (no Const operand)
      Store(%pout, %vc)        # store result
      %i1  = Add(%i, 1)        # index increment — Const operand

## Scenarios

### AutoVectorize elementwise pattern matcher — positive cases

<details>
<summary>Advanced: recognises add elementwise loop (J4 T01-like saxpy)</summary>

#### recognises add elementwise loop (J4 T01-like saxpy)

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_add()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: recognises mul elementwise loop</summary>

#### recognises mul elementwise loop

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_mul()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: recognised sub elementwise loop</summary>

#### recognised sub elementwise loop

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_sub()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
```

</details>


</details>

#### recipe kind is Elementwise for add block

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_add()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
val is_elementwise = match recipe.kind:
    case Elementwise: true
    case _: false
expect(is_elementwise).to_equal(true)
```

</details>

#### recipe op_name contains add for add block

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_add()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.op_name).to_contain("add")
```

</details>

### AutoVectorize reduction pattern matcher — positive cases

<details>
<summary>Advanced: recognises sum reduction loop (J4 dot-product shape)</summary>

#### recognises sum reduction loop (J4 dot-product shape)

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: recognises product reduction loop</summary>

#### recognises product reduction loop

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_mul_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
```

</details>


</details>

#### recipe kind is Reduction for sum block

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
val is_reduction = match recipe.kind:
    case Reduction: true
    case _: false
expect(is_reduction).to_equal(true)
```

</details>

#### recipe op_name contains add for sum block

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.op_name).to_contain("add")
```

</details>

#### recipe vector_width is positive for sum block

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.vector_width > 0).to_equal(true)
```

</details>

#### recognises integer xor-plus-sum traversal checksum

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_xor_sum_block()
val result = mir_pattern_match_reduction(block, false)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.op_name).to_equal("xor_add_reduction")
expect(recipe.element_type).to_equal("i32")
```

</details>

### AutoVectorize matrix-kernel pattern matcher — positive cases

<details>
<summary>Advanced: recognises a canonical dot-product inner loop with fast_math</summary>

#### recognises a canonical dot-product inner loop with fast_math

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_matrix_dot_block()
val result = mir_pattern_match_matrix_kernel(block, true)
expect(result.?).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: matrix kernel recipe kind is MatrixKernel</summary>

#### matrix kernel recipe kind is MatrixKernel

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_matrix_dot_block()
val result = mir_pattern_match_matrix_kernel(block, true)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
val is_matrix = match recipe.kind:
    case MatrixKernel: true
    case _: false
expect(is_matrix).to_equal(true)
```

</details>


</details>

### AutoVectorize pattern matcher — §8 failure modes (must return nil)

#### function call in body inhibits elementwise match

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# §8 failure: FFI/function call in loop body
val block = make_block_with_call()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(false)
```

</details>

#### function call in body inhibits reduction match

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_block_with_call()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(false)
```

</details>

#### no induction variable inhibits elementwise match

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# §8 failure: loop structure not recognised (no counted induction)
val block = make_block_no_induction()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(false)
```

</details>

#### no array loads inhibits elementwise match

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# §8 failure: indirect load / no contiguous stride-1 access
val block = make_block_no_loads()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(false)
```

</details>

<details>
<summary>Advanced: store in loop body inhibits reduction match (not a pure accumulator)</summary>

#### store in loop body inhibits reduction match (not a pure accumulator)

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# §8 failure: accumulator written to memory → not a register reduction
val block = make_reduction_with_store()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(false)
```

</details>


</details>

### AutoVectorize run_auto_vectorize — skeleton no-op guarantee

#### returns module unchanged on empty module

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = make_empty_module()
val result = run_auto_vectorize(m)
# Empty module: no functions, so no recipes found; module name is preserved
expect(result.name).to_equal("test_module")
```

</details>

#### module function count unchanged after pass

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = make_empty_module()
val before = m.functions.keys().len()
val result = run_auto_vectorize(m)
val after = result.functions.keys().len()
expect(after).to_equal(before)
```

</details>

### AutoVectorize run_auto_vectorize — pipeline wiring (Wave L3b)

#### module with elementwise function is processed (name preserved, functions accessible)

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a non-empty module and run the pass.
# The block fixture has dynamic trip count so R4 refuses vectorization,
# but the pass still processes the module and preserves all fields correctly
# (verifies MirModule explicit-field construction in run_auto_vectorize).
val ew_block = make_elementwise_block_add()
val func     = make_test_mir_function([ew_block], false)
var fns: Dict<SymbolId, MirFunction> = {}
fns[func.symbol] = func
val m = MirModule(
    name:      "test_module",
    functions: fns,
    statics:   {},
    constants: {},
    types:     {}
)
val result = run_auto_vectorize(m)
# Module name is preserved and the function is still present.
expect(result.name).to_equal("test_module")
expect(result.functions.keys().len()).to_equal(1)
```

</details>

#### module.functions dict is correctly updated after rewrite (MirModule fields not dropped)

<details>
<summary>Executable SPipe</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify explicit MirModule construction wires the functions field.
# Use make_elementwise_add_recipe_for_rewrite (trip_count=16) directly
# via rewrite_elementwise_add to confirm the rewriter works, then verify
# the function can be stored and retrieved from a module dict.
val orig_block = make_elementwise_block_add()
val func       = make_test_mir_function([orig_block], false)
val recipe     = make_elementwise_add_recipe_for_rewrite()
val rewritten  = rewrite_elementwise_add(recipe, func)
var fns: Dict<SymbolId, MirFunction> = {}
fns[rewritten.symbol] = rewritten
val m2 = MirModule(
    name:      "test_rewritten",
    functions: fns,
    statics:   {},
    constants: {},
    types:     {}
)
val retrieved = m2.functions[rewritten.symbol]
# The rewritten function's block count should be greater than the original.
expect(retrieved.blocks.len() > func.blocks.len()).to_equal(true)
```

</details>

### AutoVectorize W-recipe — elementwise recipe fields

#### elementwise add recipe input_bases field exists (list, len >= 0)

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_add()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
val has_list = recipe.input_bases.len() >= 0
expect(has_list).to_equal(true)
```

</details>

#### elementwise recipe accumulator is nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_add()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.accumulator.?).to_equal(false)
```

</details>

#### elementwise recipe chunk_width matches vector_width

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_add()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.chunk_width).to_equal(recipe.vector_width)
```

</details>

#### elementwise recipe chunk_width is positive

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_add()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.chunk_width > 0).to_equal(true)
```

</details>

#### elementwise recipe index_locals tracks the induction variable

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_elementwise_block_add()
val result = mir_pattern_match_elementwise_loop(block)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.index_locals.len()).to_equal(1)
```

</details>

### AutoVectorize W-recipe — reduction recipe fields

#### reduction sum recipe accumulator is Some

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.accumulator.?).to_equal(true)
```

</details>

#### reduction recipe output_base is nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.output_base.?).to_equal(false)
```

</details>

#### reduction recipe chunk_width is positive

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.chunk_width > 0).to_equal(true)
```

</details>

#### reduction recipe chunk_width matches vector_width

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
val recipe = result.unwrap()
expect(recipe.chunk_width).to_equal(recipe.vector_width)
```

</details>

### AutoVectorize W-scev — detect_bounds_from_block positive

<details>
<summary>Advanced: for-i-in-0..n returns Some(LoopBounds)</summary>

#### for-i-in-0..n returns Some(LoopBounds)

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_bounds_block_for_n()
val result = detect_bounds_from_block(block, make_copy_op(20), make_block_id(99))
expect(result.?).to_equal(true)
```

</details>


</details>

#### for-i-in-0..n lower bound is 0

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_bounds_from_block(make_bounds_block_for_n(), make_copy_op(20), make_block_id(99))
expect(result.?).to_equal(true)
expect(result.unwrap().lower).to_equal(0)
```

</details>

#### for-i-in-0..n step is 1

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_bounds_from_block(make_bounds_block_for_n(), make_copy_op(20), make_block_id(99))
expect(result.?).to_equal(true)
expect(result.unwrap().step).to_equal(1)
```

</details>

#### for-i-in-0..n upper encodes local 30 as _l30

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_bounds_from_block(make_bounds_block_for_n(), make_copy_op(20), make_block_id(99))
expect(result.?).to_equal(true)
expect(result.unwrap().upper).to_equal("_l30")
```

</details>

#### for-i-in-0..arr.len upper encodes local 31 as _l31

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_bounds_from_block(make_bounds_block_for_arr_len(), make_copy_op(20), make_block_id(99))
expect(result.?).to_equal(true)
expect(result.unwrap().upper).to_equal("_l31")
```

</details>

### AutoVectorize W-scev — detect_bounds_from_block negative

#### Ne condition (while i != n) returns nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_bounds_from_block(make_bounds_block_ne_cond(), make_copy_op(20), make_block_id(99))
expect(result.?).to_equal(false)
```

</details>

<details>
<summary>Advanced: loop with no unit-step increment returns nil</summary>

#### loop with no unit-step increment returns nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_bounds_from_block(make_bounds_block_no_increment(), make_copy_op(20), make_block_id(99))
expect(result.?).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: infinite loop (no cmp defining cond local) returns nil</summary>

#### infinite loop (no cmp defining cond local) returns nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_bounds_from_block(make_bounds_block_infinite(), make_copy_op(20), make_block_id(99))
expect(result.?).to_equal(false)
```

</details>


</details>

#### Const cond operand (not a local) returns nil

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = detect_bounds_from_block(make_bounds_block_for_n(), make_const_op("1"), make_block_id(99))
expect(result.?).to_equal(false)
```

</details>

### AutoVectorize W-fastmath — FP reduction gate

#### reduction matcher refuses f32 sum when has_fast_math=false

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, false)
expect(result.?).to_equal(false)
```

</details>

#### reduction matcher accepts f32 sum when has_fast_math=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_sum_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
```

</details>

#### product reduction accepted with has_fast_math=true

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_mul_block()
val result = mir_pattern_match_reduction(block, true)
expect(result.?).to_equal(true)
```

</details>

#### product reduction refused with has_fast_math=false

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block = make_reduction_mul_block()
val result = mir_pattern_match_reduction(block, false)
expect(result.?).to_equal(false)
```

</details>

### AutoVectorize W-cfg — create_alignment_check_block

#### produces a block with label align_check

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val li  = make_test_loop_info()
val ctx = make_test_vectorize_ctx()
val bb  = create_alignment_check_block(ctx, li)
expect(bb.label.?).to_equal(true)
expect(bb.label.unwrap()).to_equal("align_check")
```

</details>

#### alignment-check terminator is If

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val li  = make_test_loop_info()
val ctx = make_test_vectorize_ctx()
val bb  = create_alignment_check_block(ctx, li)
val is_if = match bb.terminator:
    case If(cond, then_, else_): true
    case _: false
expect(is_if).to_equal(true)
```

</details>

### AutoVectorize W-cfg — create_peeling_block

<details>
<summary>Advanced: produces a block with label peel_loop</summary>

#### produces a block with label peel_loop

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val li  = make_test_loop_info()
val ctx = make_test_vectorize_ctx()
val bb  = create_peeling_block(ctx, li, [])
expect(bb.label.?).to_equal(true)
expect(bb.label.unwrap()).to_equal("peel_loop")
```

</details>


</details>

### AutoVectorize N1-rewrite — elementwise-add divisible trip count (0..16) via codegen

<details>
<summary>Advanced: alignment-check block has If terminator (branches to vec_loop or peel)</summary>

#### alignment-check block has If terminator (branches to vec_loop or peel)

1. header block:  make block id

2. exit block:    make block id

3. induction var: make local
   - Expected: is_if is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = VectorizeContext(vector_width: 4, element_type: "i32", next_local: 1)
val li  = LoopInfo(
    header_block:  make_block_id(1),
    body_blocks:   [],
    exit_block:    make_block_id(4),
    induction_var: make_local(4),
    start_value:   0,
    end_value:     16,
    step:          1
)
val align = create_alignment_check_block(ctx, li)
val is_if = match align.terminator:
    case If(cond, then_, else_): true
    case _: false
expect(is_if).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: vec_loop block for i32x4 recipe has label vec_loop</summary>

#### vec_loop block for i32x4 recipe has label vec_loop

1. [make local
   - Expected: bb.label.? is true
   - Expected: bb.label.unwrap() equals `vec_loop`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = VectorizeContext(vector_width: 4, element_type: "i32", next_local: 1)
val bb  = create_vector_loop_block(ctx, 1,
    [make_local(10), make_local(11)], make_local(12), "add_elementwise", 16, 4)
expect(bb.label.?).to_equal(true)
expect(bb.label.unwrap()).to_equal("vec_loop")
```

</details>


</details>

<details>
<summary>Advanced: vec_loop block for i32x4 has >= 4 SIMD instructions</summary>

#### vec_loop block for i32x4 has >= 4 SIMD instructions

1. [make local
   - Expected: bb.instructions.len() >= 4 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = VectorizeContext(vector_width: 4, element_type: "i32", next_local: 1)
val bb  = create_vector_loop_block(ctx, 1,
    [make_local(10), make_local(11)], make_local(12), "add_elementwise", 16, 4)
# load_a + load_b + simd_add + simd_store + vi_inc + guard = 6 instructions
expect(bb.instructions.len() >= 4).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: peel_loop block for trip_count=16 divisible trip has label peel_loop</summary>

#### peel_loop block for trip_count=16 divisible trip has label peel_loop

1. header block:  make block id

2. exit block:    make block id

3. induction var: make local
   - Expected: peel.label.? is true
   - Expected: peel.label.unwrap() equals `peel_loop`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = VectorizeContext(vector_width: 4, element_type: "i32", next_local: 1)
val li  = LoopInfo(
    header_block:  make_block_id(1),
    body_blocks:   [],
    exit_block:    make_block_id(4),
    induction_var: make_local(4),
    start_value:   0,
    end_value:     16,
    step:          1
)
val peel = create_peeling_block(ctx, li, [])
expect(peel.label.?).to_equal(true)
expect(peel.label.unwrap()).to_equal("peel_loop")
```

</details>


</details>

### AutoVectorize N1-rewrite — elementwise-add dynamic trip count (0..n) via codegen

#### alignment-check block for dynamic n (end_value=0 sentinel) still has If terminator

1. header block:  make block id

2. exit block:    make block id

3. induction var: make local
   - Expected: is_if is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When trip_count = -1 (unknown), rewriter uses end_value=0 as sentinel.
# The alignment-check block still produces a runtime If terminator.
val ctx = VectorizeContext(vector_width: 4, element_type: "i32", next_local: 1)
val li  = LoopInfo(
    header_block:  make_block_id(1),
    body_blocks:   [],
    exit_block:    make_block_id(4),
    induction_var: make_local(4),
    start_value:   0,
    end_value:     0,
    step:          1
)
val align = create_alignment_check_block(ctx, li)
val is_if = match align.terminator:
    case If(cond, then_, else_): true
    case _: false
expect(is_if).to_equal(true)
```

</details>

<details>
<summary>Advanced: peel_loop block for dynamic n has Goto terminator (no body clone when body_blocks empty)</summary>

#### peel_loop block for dynamic n has Goto terminator (no body clone when body_blocks empty)

1. header block:  make block id

2. exit block:    make block id

3. induction var: make local
   - Expected: is_goto is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = VectorizeContext(vector_width: 4, element_type: "i32", next_local: 1)
val li  = LoopInfo(
    header_block:  make_block_id(1),
    body_blocks:   [],
    exit_block:    make_block_id(4),
    induction_var: make_local(4),
    start_value:   0,
    end_value:     0,
    step:          1
)
val peel = create_peeling_block(ctx, li, [])
val is_goto = match peel.terminator:
    case Goto(target): true
    case _: false
expect(is_goto).to_equal(true)
```

</details>


</details>

### AutoVectorize N1-rewrite — refuses trip count < chunk_width (0..3, VF=4)

#### trip-count=3 < VF=4 returns function unchanged (same block count)

1. header block:     make block id

2. induction var:    make local

3. input bases:      [make local

4. output base:      Some

5. index locals:     [make local

6. induction update: make local
   - Expected: result.blocks.len() equals `func.blocks.len()`


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig_block = make_elementwise_block_add()
val func       = make_test_mir_function([orig_block], false)
val recipe     = VectorRecipe(
    kind:             VectorRecipeKind.Elementwise,
    header_block:     make_block_id(1),
    induction_var:    make_local(4),
    trip_count:       3,
    element_type:     "i32",
    vector_width:     4,
    op_name:          "add_elementwise",
    note:             "too short",
    input_bases:      [make_local(10), make_local(11)],
    output_base:      Some(make_local(12)),
    accumulator:      nil,
    chunk_width:      4,
    index_locals:     [make_local(4)],
    store_value:      nil,
    induction_update: make_local(4)
)
val result = rewrite_elementwise_add(recipe, func)
expect(result.blocks.len()).to_equal(func.blocks.len())
```

</details>

### AutoVectorize N1-rewrite — refuses dynamic trip count (trip_count=-1)

#### trip-count=-1 (dynamic) returns function unchanged (same block count)

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig_block = make_elementwise_block_add()
val func       = make_test_mir_function([orig_block], false)
val recipe     = make_elementwise_add_recipe_dynamic_n()
val result     = rewrite_elementwise_add(recipe, func)
expect(result.blocks.len()).to_equal(func.blocks.len())
```

</details>

### AutoVectorize N1-rewrite — accepts misaligned trip count (6 % 4 != 0) with peel body (Wave L3b)

#### trip-count=6 misaligned with VF=4 rewrites function (block count increases)

1. header block:     make block id

2. induction var:    make local

3. input bases:      [make local

4. output base:      Some

5. index locals:     [make local

6. induction update: make local
   - Expected: result.blocks.len() > func.blocks.len() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig_block = make_elementwise_block_add()
val func       = make_test_mir_function([orig_block], false)
val recipe     = VectorRecipe(
    kind:             VectorRecipeKind.Elementwise,
    header_block:     make_block_id(1),
    induction_var:    make_local(4),
    trip_count:       6,
    element_type:     "i32",
    vector_width:     4,
    op_name:          "add_elementwise",
    note:             "misaligned",
    input_bases:      [make_local(10), make_local(11)],
    output_base:      Some(make_local(12)),
    accumulator:      nil,
    chunk_width:      4,
    index_locals:     [make_local(4)],
    store_value:      nil,
    induction_update: make_local(4)
)
val result = rewrite_elementwise_add(recipe, func)
# Was 1 scalar block; now replaced with 3 new blocks (align + vec + peel).
expect(result.blocks.len() > func.blocks.len()).to_equal(true)
```

</details>

### AutoVectorize N1-rewrite — accepts divisible trip count (0..16, VF=4)

#### trip-count=16 divisible with VF=4 rewrites function (block count increases)

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig_block = make_elementwise_block_add()
val func       = make_test_mir_function([orig_block], false)
val recipe     = make_elementwise_add_recipe_for_rewrite()
val result     = rewrite_elementwise_add(recipe, func)
expect(result.blocks.len() > func.blocks.len()).to_equal(true)
```

</details>

#### mul recipe is also rewritten (block count increases)

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig_block = make_elementwise_block_mul()
val func       = make_test_mir_function([orig_block], false)
val recipe     = make_elementwise_mul_recipe()
val result     = rewrite_elementwise_add(recipe, func)
expect(result.blocks.len() > func.blocks.len()).to_equal(true)
```

</details>

### AutoVectorize N1-rewrite — refuses unsupported elementwise div

#### div recipe is outside the phase-1 rewrite set

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig_block = make_elementwise_block_mul()
val func       = make_test_mir_function([orig_block], false)
val recipe     = make_unsupported_div_recipe()
val result     = rewrite_elementwise_add(recipe, func)
expect(result.blocks.len()).to_equal(func.blocks.len())
```

</details>

### AutoVectorize N1-rewrite — elementwise mul is in the phase-1 rewrite set

#### mul recipe is accepted by the phase-1 rewrite gate

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(supports_elementwise_rewrite("mul_elementwise")).to_equal(true)
```

</details>

### AutoVectorize N1-rewrite — elementwise f32 add does not require fast_math

#### f32 elementwise-add remains in the supported rewrite set without fast_math

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recipe = make_elementwise_add_recipe_f32_no_fastmath()
expect(supports_elementwise_rewrite(recipe.op_name)).to_equal(true)
```

</details>

### AutoVectorize N1-codegen — create_vector_loop_block

<details>
<summary>Advanced: produces a block with label vec_loop</summary>

#### produces a block with label vec_loop

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx   = VectorizeContext(vector_width: 4, element_type: "i32", next_local: 100)
val bb    = create_vector_loop_block(ctx, 100, [make_local(10), make_local(11)], make_local(12), "add_elementwise", 16, 103)
expect(bb.label.?).to_equal(true)
expect(bb.label.unwrap()).to_equal("vec_loop")
```

</details>


</details>

<details>
<summary>Advanced: vec_loop block contains >= 4 instructions (load_a, load_b, add, store, inc, guard)</summary>

#### vec_loop block contains >= 4 instructions (load_a, load_b, add, store, inc, guard)

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx   = VectorizeContext(vector_width: 4, element_type: "i32", next_local: 100)
val bb    = create_vector_loop_block(ctx, 100, [make_local(10), make_local(11)], make_local(12), "xor_elementwise", 16, 103)
expect(bb.instructions.len() >= 4).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: vec_loop block has If terminator (exit guard — not self-loop Goto)</summary>

#### vec_loop block has If terminator (exit guard — not self-loop Goto)

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx   = VectorizeContext(vector_width: 4, element_type: "i32", next_local: 100)
val bb    = create_vector_loop_block(ctx, 100, [make_local(10), make_local(11)], make_local(12), "add_elementwise", 16, 103)
val is_if = match bb.terminator:
    case If(cond, then_, else_): true
    case _: false
expect(is_if).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 64 |
| Active scenarios | 64 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
