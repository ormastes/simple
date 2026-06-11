# Js Jit Optimizer Specification

> 1. JitIR LoadConst

<!-- sdn-diagram:id=js_jit_optimizer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=js_jit_optimizer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

js_jit_optimizer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=js_jit_optimizer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Jit Optimizer Specification

## Scenarios

### JsJitOptimizer

#### folds numeric arithmetic and removes dead source constants and guards

1. JitIR LoadConst
2. JitIR LoadConst
3. JitIR Add
4. JitIR Return
   - Expected: optimized.len() equals `2`
   - Expected: _count_load_consts(optimized) equals `1`
   - Expected: _count_guards(optimized) equals `0`
   - Expected: _first_number_const(optimized) equals `2:3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val optimizer = OptimizingCompiler.create(Logger.new("js-jit-optimizer-spec", LogLevel.Error))
val ir = [
    JitIR.LoadConst(reg: 0, value: JsValue.Number(v: 1.0)),
    JitIR.LoadConst(reg: 1, value: JsValue.Number(v: 2.0)),
    JitIR.Add(dst: 2, lhs: 0, rhs: 1),
    JitIR.Return(reg: 2)
]

val optimized = optimizer.optimize(ir, [JitTypeTag.TagNumber])

expect(optimized.len()).to_equal(2)
expect(_count_load_consts(optimized)).to_equal(1)
expect(_count_guards(optimized)).to_equal(0)
expect(_first_number_const(optimized)).to_equal("2:3")
```

</details>

#### repeats optimization until folded intermediates are eliminated

1. JitIR LoadConst
2. JitIR LoadConst
3. JitIR Add
4. JitIR LoadConst
5. JitIR Add
6. JitIR Return
   - Expected: optimized.len() equals `2`
   - Expected: _count_load_consts(optimized) equals `1`
   - Expected: _count_guards(optimized) equals `0`
   - Expected: _first_number_const(optimized) equals `4:7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val optimizer = OptimizingCompiler.create(Logger.new("js-jit-optimizer-spec", LogLevel.Error))
val ir = [
    JitIR.LoadConst(reg: 0, value: JsValue.Number(v: 1.0)),
    JitIR.LoadConst(reg: 1, value: JsValue.Number(v: 2.0)),
    JitIR.Add(dst: 2, lhs: 0, rhs: 1),
    JitIR.LoadConst(reg: 3, value: JsValue.Number(v: 4.0)),
    JitIR.Add(dst: 4, lhs: 2, rhs: 3),
    JitIR.Return(reg: 4)
]

val optimized = optimizer.optimize(ir, [JitTypeTag.TagNumber])

expect(optimized.len()).to_equal(2)
expect(_count_load_consts(optimized)).to_equal(1)
expect(_count_guards(optimized)).to_equal(0)
expect(_first_number_const(optimized)).to_equal("4:7")
```

</details>

#### folds profiled division and modulo without leaving generic arithmetic

1. JitIR LoadConst
2. JitIR LoadConst
3. JitIR Div
4. JitIR LoadConst
5. JitIR Mod
6. JitIR Return
   - Expected: optimized.len() equals `2`
   - Expected: _count_load_consts(optimized) equals `1`
   - Expected: _count_guards(optimized) equals `0`
   - Expected: _first_number_const(optimized) equals `4:0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val optimizer = OptimizingCompiler.create(Logger.new("js-jit-optimizer-spec", LogLevel.Error))
val ir = [
    JitIR.LoadConst(reg: 0, value: JsValue.Number(v: 9.0)),
    JitIR.LoadConst(reg: 1, value: JsValue.Number(v: 2.0)),
    JitIR.Div(dst: 2, lhs: 0, rhs: 1),
    JitIR.LoadConst(reg: 3, value: JsValue.Number(v: 4.0)),
    JitIR.Mod(dst: 4, lhs: 2, rhs: 3),
    JitIR.Return(reg: 4)
]

val optimized = optimizer.optimize(ir, [JitTypeTag.TagNumber])

expect(optimized.len()).to_equal(2)
expect(_count_load_consts(optimized)).to_equal(1)
expect(_count_guards(optimized)).to_equal(0)
expect(_first_number_const(optimized)).to_equal("4:0.5")
```

</details>

#### folds compare and unary numeric operations

1. JitIR LoadConst
2. JitIR Negate
3. JitIR LoadConst
4. JitIR Compare
5. JitIR Return
   - Expected: optimized.len() equals `2`
   - Expected: _count_load_consts(optimized) equals `1`
   - Expected: _count_guards(optimized) equals `0`
   - Expected: _first_bool_const(optimized) equals `3:true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val optimizer = OptimizingCompiler.create(Logger.new("js-jit-optimizer-spec", LogLevel.Error))
val ir = [
    JitIR.LoadConst(reg: 0, value: JsValue.Number(v: 5.0)),
    JitIR.Negate(dst: 1, src: 0),
    JitIR.LoadConst(reg: 2, value: JsValue.Number(v: -5.0)),
    JitIR.Compare(dst: 3, lhs: 1, rhs: 2, op: "eq"),
    JitIR.Return(reg: 3)
]

val optimized = optimizer.optimize(ir, [JitTypeTag.TagNumber])

expect(optimized.len()).to_equal(2)
expect(_count_load_consts(optimized)).to_equal(1)
expect(_count_guards(optimized)).to_equal(0)
expect(_first_bool_const(optimized)).to_equal("3:true")
```

</details>

#### executes specialized division and modulo for profiled nonconstant inputs

1. JitIR IntDiv
2. JitIR IntMod
3. JitIR Return
4. JsValue Number
5. JsValue Number
   - Expected: result.is_ok() is true
6. JsValue Number
   - Expected: n equals `0.5`
7. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val executor = JitExecutor.create(Logger.new("js-jit-optimizer-spec", LogLevel.Error))
val ir = [
    JitIR.IntDiv(dst: 2, lhs: 0, rhs: 1),
    JitIR.IntMod(dst: 3, lhs: 2, rhs: 1),
    JitIR.Return(reg: 3)
]

val result = executor.execute(ir, [
    JsValue.Number(v: 9.0),
    JsValue.Number(v: 2.0)
])

expect(result.is_ok()).to_equal(true)
match result.unwrap():
    JsValue.Number(n):
        expect(n).to_equal(0.5)
    _:
        fail("JIT executor did not return a numeric result for specialized modulo")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/js_jit_optimizer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JsJitOptimizer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
