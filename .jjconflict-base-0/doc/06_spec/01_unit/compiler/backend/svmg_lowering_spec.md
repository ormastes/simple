# Svmg Lowering Specification

> Tests covering SVM-G Task D4 lowering — expect(add(1,2)).to_equal(3), SVM-G Task D4 lowering — bounded for-range loop, SVM-G Task D4 lowering — fixed-size array sum, SVM-G Task D4 lowering — if/elif/else, SVM-G Task D4 lowering — bounded while loop, SVM-G Task D4 lowering — print of a string literal, SVM-G Task D4 lowering — float arithmetic and comparison, SVM-G Task D4 lowering — rejects excluded constructs (design doc §4.4), SVM-G Task D4 lowering — rejects still-deferred constructs (not yet implemented).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Svmg Lowering Specification

## Scenarios

### SVM-G Task D4 lowering — expect(add(1,2)).to_equal(3)

#### lowers a non-recursive helper-fn call plus expect().to_equal() and executes it correctly on D2's VM

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers a non-recursive helper-fn call plus expect().to_equal() and executes it correctly on D2's VM")
val a_sym = SymbolId(id: 1)
val b_sym = SymbolId(id: 2)
val add_fn = SvmgHelperFn(
    name: "add",
    params: [param(a_sym, "a"), param(b_sym, "b")],
    body: block_with_tail([], binop(HirBinOp.Add, var_(a_sym), var_(b_sym))),
)
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: expect_to_equal(
        call(named_var(SymbolId(id: 10), "add"), [int_lit(1), int_lit(2)]),
        int_lit(3),
    ))),
])
val prog = lower_svmg_program(body, [add_fn], 1000)
assert_true(prog.ok)
val result = assemble_and_run(prog.code, prog.step_budget, prog.entry_pc)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records.len(), 1)
assert_equal(records[0].passed, 1)
assert_equal(records[0].value, 3)
```

</details>

### SVM-G Task D4 lowering — bounded for-range loop

<details>
<summary>Advanced: sums 0..5 (exclusive) via a bounded for loop and checks the total with expect().to_equal()</summary>

#### sums 0..5 (exclusive) via a bounded for loop and checks the total with expect().to_equal()

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums 0..5 (exclusive) via a bounded for loop and checks the total with expect().to_equal()")
val i_sym = SymbolId(id: 1)
val sum_sym = SymbolId(id: 2)
val range_expr = e(HirExprKind.Range(start: int_lit(0), end: int_lit(5), inclusive: false, step: nil))
val loop_body = block_no_tail([
    s(HirStmtKind.Assign(target: var_(sum_sym), op: HirAssignOp.Add, value: var_(i_sym))),
])
val body = block_no_tail([
    s(HirStmtKind.Let(symbol: sum_sym, type_: ty(), init: int_lit(0))),
    s(HirStmtKind.Expr(expr: e(HirExprKind.For(var_: i_sym, iter: range_expr, body: loop_body, label: nil)))),
    s(HirStmtKind.Expr(expr: expect_to_equal(var_(sum_sym), int_lit(10)))),
])
val prog = lower_svmg_program(body, [], 5000)
assert_true(prog.ok)
val result = assemble_and_run(prog.code, prog.step_budget, prog.entry_pc)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records.len(), 1)
assert_equal(records[0].passed, 1)
assert_equal(records[0].value, 10)
```

</details>


</details>

### SVM-G Task D4 lowering — fixed-size array sum

#### sums a fixed-size array via for-x-in-array and checks the total with expect().to_equal()

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums a fixed-size array via for-x-in-array and checks the total with expect().to_equal()")
val arr_sym = SymbolId(id: 1)
val x_sym = SymbolId(id: 2)
val sum_sym = SymbolId(id: 3)
val arr_lit = e(HirExprKind.ArrayLit(elements: [int_lit(1), int_lit(2), int_lit(3), int_lit(4), int_lit(5)], type_: nil))
val body = block_no_tail([
    s(HirStmtKind.Let(symbol: arr_sym, type_: ty(), init: arr_lit)),
    s(HirStmtKind.Let(symbol: sum_sym, type_: ty(), init: int_lit(0))),
    s(HirStmtKind.Expr(expr: e(HirExprKind.For(var_: x_sym, iter: var_(arr_sym), body: block_no_tail([
        s(HirStmtKind.Assign(target: var_(sum_sym), op: HirAssignOp.Add, value: var_(x_sym))),
    ]), label: nil)))),
    s(HirStmtKind.Expr(expr: expect_to_equal(var_(sum_sym), int_lit(15)))),
])
val prog = lower_svmg_program(body, [], 5000)
assert_true(prog.ok)
val result = assemble_and_run(prog.code, prog.step_budget, prog.entry_pc)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records.len(), 1)
assert_equal(records[0].passed, 1)
assert_equal(records[0].value, 15)
```

</details>

### SVM-G Task D4 lowering — if/elif/else

#### picks the elif branch (nested If inside the else_ block) and executes the right accumulation on D2's VM

- picks the elif branch (nested If inside the else_ block) and executes the right accumulation on D2's VM


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("picks the elif branch (nested If inside the else_ block) and executes the right accumulation on D2's VM")
val x_sym = SymbolId(id: 1)
val total_sym = SymbolId(id: 2)
# if x > 10: total += 100
# elif x > 5: total += 10   <- x == 7 takes this branch
# else: total += 1
val inner_if = e(HirExprKind.If(
    cond: binop(HirBinOp.Gt, var_(x_sym), int_lit(5)),
    then_: block_no_tail([assign(var_(total_sym), HirAssignOp.Add, int_lit(10))]),
    else_: block_no_tail([assign(var_(total_sym), HirAssignOp.Add, int_lit(1))]),
))
val outer_if = e(HirExprKind.If(
    cond: binop(HirBinOp.Gt, var_(x_sym), int_lit(10)),
    then_: block_no_tail([assign(var_(total_sym), HirAssignOp.Add, int_lit(100))]),
    else_: block_no_tail([s(HirStmtKind.Expr(expr: inner_if))]),
))
val body = block_no_tail([
    s(HirStmtKind.Let(symbol: x_sym, type_: ty(), init: int_lit(7))),
    s(HirStmtKind.Let(symbol: total_sym, type_: ty(), init: int_lit(0))),
    s(HirStmtKind.Expr(expr: outer_if)),
    s(HirStmtKind.Expr(expr: expect_to_equal(var_(total_sym), int_lit(10)))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_true(prog.ok)
val result = assemble_and_run(prog.code, prog.step_budget, prog.entry_pc)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records.len(), 1)
assert_equal(records[0].passed, 1)
assert_equal(records[0].value, 10)
```

</details>

### SVM-G Task D4 lowering — bounded while loop

<details>
<summary>Advanced: sums 0..5 (exclusive) via a while loop (step-budget backstop) and checks the total with expect().to_equal()</summary>

#### sums 0..5 (exclusive) via a while loop (step-budget backstop) and checks the total with expect().to_equal()

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sums 0..5 (exclusive) via a while loop (step-budget backstop) and checks the total with expect().to_equal()")
val i_sym = SymbolId(id: 1)
val sum_sym = SymbolId(id: 2)
val loop_body = block_no_tail([
    assign(var_(sum_sym), HirAssignOp.Add, var_(i_sym)),
    assign(var_(i_sym), HirAssignOp.Add, int_lit(1)),
])
val body = block_no_tail([
    s(HirStmtKind.Let(symbol: i_sym, type_: ty(), init: int_lit(0))),
    s(HirStmtKind.Let(symbol: sum_sym, type_: ty(), init: int_lit(0))),
    s(HirStmtKind.Expr(expr: e(HirExprKind.While(
        cond: binop(HirBinOp.Lt, var_(i_sym), int_lit(5)),
        body: loop_body,
        label: nil,
    )))),
    s(HirStmtKind.Expr(expr: expect_to_equal(var_(sum_sym), int_lit(10)))),
])
val prog = lower_svmg_program(body, [], 5000)
assert_true(prog.ok)
val result = assemble_and_run(prog.code, prog.step_budget, prog.entry_pc)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records.len(), 1)
assert_equal(records[0].passed, 1)
assert_equal(records[0].value, 10)
```

</details>


</details>

### SVM-G Task D4 lowering — print of a string literal

#### lowers print(\

- lowers print(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowers print(\")
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: call(named_var(SymbolId(id: 40), "print"), [string_lit("hi")]))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_true(prog.ok)
val result = assemble_and_run(prog.code, prog.step_budget, prog.entry_pc)
assert_equal(read_log(result.arena, result.log_cap), "hi")
```

</details>

### SVM-G Task D4 lowering — float arithmetic and comparison

#### computes 1.5 + 2.5 via FADD and checks it against 4.0 via FEQ (expect().to_equal())

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes 1.5 + 2.5 via FADD and checks it against 4.0 via FEQ (expect().to_equal())")
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: expect_to_equal(
        binop(HirBinOp.Add, float_lit(1.5), float_lit(2.5)),
        float_lit(4.0),
    ))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_true(prog.ok)
val result = assemble_and_run(prog.code, prog.step_budget, prog.entry_pc)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records.len(), 1)
assert_equal(records[0].passed, 1)
assert_equal(records[0].value, expected_signed_i32_bits(4.0))
```

</details>

#### takes the FGT branch of an if (3.5 > 2.0) and accumulates the correct total

- takes the FGT branch of an if (3.5 > 2.0) and accumulates the correct total


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes the FGT branch of an if (3.5 > 2.0) and accumulates the correct total")
val r_sym = SymbolId(id: 1)
val body = block_no_tail([
    s(HirStmtKind.Let(symbol: r_sym, type_: ty(), init: int_lit(0))),
    s(HirStmtKind.Expr(expr: e(HirExprKind.If(
        cond: binop(HirBinOp.Gt, float_lit(3.5), float_lit(2.0)),
        then_: block_no_tail([assign(var_(r_sym), HirAssignOp.Add, int_lit(1))]),
        else_: block_no_tail([assign(var_(r_sym), HirAssignOp.Add, int_lit(0))]),
    )))),
    s(HirStmtKind.Expr(expr: expect_to_equal(var_(r_sym), int_lit(1)))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_true(prog.ok)
val result = assemble_and_run(prog.code, prog.step_budget, prog.entry_pc)
val records = read_records(result.arena, result.log_cap, result.record_count)
assert_equal(records.len(), 1)
assert_equal(records[0].passed, 1)
assert_equal(records[0].value, 1)
```

</details>

### SVM-G Task D4 lowering — rejects excluded constructs (design doc §4.4)

#### rejects closures (Lambda)

- rejects closures (Lambda)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects closures (Lambda)")
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: e(HirExprKind.Lambda(params: [], body: int_lit(0), captures: [])))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_false(prog.ok)
assert_contains(prog.error, "closures")
```

</details>

#### rejects GC types (struct-literal construction)

- rejects GC types (struct-literal construction)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects GC types (struct-literal construction)")
val struct_ty = HirType(kind: HirTypeKind.Named(symbol: SymbolId(id: 99), args: []), span: Span.empty())
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: e(HirExprKind.StructLit(type_: struct_ty, fields: [])))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_false(prog.ok)
assert_contains(prog.error, "GC types")
```

</details>

#### rejects actors/async (await)

- rejects actors/async (await)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects actors/async (await)")
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: e(HirExprKind.Await(expr: int_lit(0))))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_false(prog.ok)
assert_contains(prog.error, "actors/async")
```

</details>

#### rejects text manipulation beyond literals (string interpolation)

- rejects text manipulation beyond literals (string interpolation)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects text manipulation beyond literals (string interpolation)")
val interp = HirInterpolation(expr: int_lit(1), has_format: false, format: "", span: Span.empty())
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: e(HirExprKind.StringLit(value: "x={0}", interpolations: [interp])))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_false(prog.ok)
assert_contains(prog.error, "text manipulation")
```

</details>

#### rejects dictionaries (DictLit)

- rejects dictionaries (DictLit)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects dictionaries (DictLit)")
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: e(HirExprKind.DictLit(entries: [], key_type: ty(), value_type: nil)))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_false(prog.ok)
assert_contains(prog.error, "dictionaries")
```

</details>

#### rejects recursion (a helper fn calling itself)

- rejects recursion (a helper fn calling itself)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects recursion (a helper fn calling itself)")
val n_sym = SymbolId(id: 1)
val bad_fn = SvmgHelperFn(
    name: "bad",
    params: [param(n_sym, "n")],
    body: block_with_tail([], call(named_var(SymbolId(id: 20), "bad"), [var_(n_sym)])),
)
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: expect_to_equal(call(named_var(SymbolId(id: 21), "bad"), [int_lit(1)]), int_lit(1)))),
])
val prog = lower_svmg_program(body, [bad_fn], 1000)
assert_false(prog.ok)
assert_contains(prog.error, "recursion")
```

</details>

### SVM-G Task D4 lowering — rejects still-deferred constructs (not yet implemented)

#### rejects print of a non-string-literal argument (e.g. an integer)

- rejects print of a non-string-literal argument (e.g. an integer)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects print of a non-string-literal argument (e.g. an integer)")
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: call(named_var(SymbolId(id: 41), "print"), [int_lit(7)]))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_false(prog.ok)
assert_contains(prog.error, "not yet implemented")
```

</details>

#### rejects compound assignment on a float local instead of silently emitting the integer opcode

- rejects compound assignment on a float local instead of silently emitting the integer opcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects compound assignment on a float local instead of silently emitting the integer opcode")
val f_sym = SymbolId(id: 1)
val body = block_no_tail([
    s(HirStmtKind.Let(symbol: f_sym, type_: float_ty(), init: float_lit(1.0))),
    assign(HirExpr(kind: HirExprKind.Var(symbol: f_sym), has_type_: true, type_: float_ty(), span: Span.empty()), HirAssignOp.Add, float_lit(1.0)),
])
val prog = lower_svmg_program(body, [], 1000)
assert_false(prog.ok)
assert_contains(prog.error, "float local")
```

</details>

#### rejects REM on float operands instead of silently emitting the integer REM opcode

- rejects REM on float operands instead of silently emitting the integer REM opcode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects REM on float operands instead of silently emitting the integer REM opcode")
val body = block_no_tail([
    s(HirStmtKind.Expr(expr: expect_to_equal(binop(HirBinOp.Mod, float_lit(5.0), float_lit(2.0)), float_lit(1.0)))),
])
val prog = lower_svmg_program(body, [], 1000)
assert_false(prog.ok)
assert_contains(prog.error, "float operands")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/svmg_lowering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SVM-G Task D4 lowering — expect(add(1,2)).to_equal(3), SVM-G Task D4 lowering — bounded for-range loop, SVM-G Task D4 lowering — fixed-size array sum, SVM-G Task D4 lowering — if/elif/else, SVM-G Task D4 lowering — bounded while loop, SVM-G Task D4 lowering — print of a string literal, SVM-G Task D4 lowering — float arithmetic and comparison, SVM-G Task D4 lowering — rejects excluded constructs (design doc §4.4), SVM-G Task D4 lowering — rejects still-deferred constructs (not yet implemented).
- SVM-G Task D4 lowering — expect(add(1,2)).to_equal(3)
- SVM-G Task D4 lowering — bounded for-range loop
- SVM-G Task D4 lowering — fixed-size array sum
- SVM-G Task D4 lowering — if/elif/else
- SVM-G Task D4 lowering — bounded while loop
- SVM-G Task D4 lowering — print of a string literal
- SVM-G Task D4 lowering — float arithmetic and comparison
- SVM-G Task D4 lowering — rejects excluded constructs (design doc §4.4)
- SVM-G Task D4 lowering — rejects still-deferred constructs (not yet implemented)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `e5a471907c8d9bfac3687ef5963a9637bd047fed90efda161903c96fc50f1f90`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5a471907c8d9bfac3687ef5963a9637bd047fed90efda161903c96fc50f1f90`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5a471907c8d9bfac3687ef5963a9637bd047fed90efda161903c96fc50f1f90`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/svmg_lowering_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/svmg_lowering_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/svmg_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/svmg_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/svmg_lowering_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a non-recursive helper-fn call plus expect().to_equal() and executes it correctly on D2's VM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/svmg_lowering_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums 0..5 (exclusive) via a bounded for loop and checks the total with expect().to_equal()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/svmg_lowering_spec.spl:156:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums a fixed-size array via for-x-in-array and checks the total with expect().to_equal()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
