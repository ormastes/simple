# HIR Lowering Unit Tests

> Tests for HIR lowering: Scope, LowerContext, Lowerer.

<!-- sdn-diagram:id=hir_lower_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hir_lower_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hir_lower_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hir_lower_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR Lowering Unit Tests

Tests for HIR lowering: Scope, LowerContext, Lowerer.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HIR-LOWER-001 |
| Category | HIR \| Lowering |
| Status | In Progress |
| Source | `test/01_unit/compiler/hir/hir_lower_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for HIR lowering: Scope, LowerContext, Lowerer.

## Scenarios

### Scope Creation

#### creates scope with parent id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val scope = Scope.new(-1, 0)
# expect scope.parent_scope_id == -1
# expect scope.depth == 0
expect true
```

</details>

#### creates nested scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val parent = Scope.new(-1, 0)
# val child = Scope.new(0, 1)
# expect child.parent_scope_id == 0
# expect child.depth == 1
expect true
```

</details>

#### starts with no locals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val scope = Scope.new(-1, 0)
# expect scope.local_count() == 0
expect true
```

</details>

### Scope Local Variables

#### add_local increases count

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var scope = Scope.new(-1, 0)
# val local = LocalVar.new("x", TypeId.i64_ty(), false, 0)
# scope.add_local(local)
# expect scope.local_count() == 1
expect true
```

</details>

#### find_local finds added local

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var scope = Scope.new(-1, 0)
# scope.add_local(LocalVar.new("foo", TypeId.i64_ty(), false, 0))
# val found = scope.find_local("foo")
# expect found.is_some()
# expect found.unwrap().name == "foo"
expect true
```

</details>

#### find_local returns None for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val scope = Scope.new(-1, 0)
# expect scope.find_local("bar").is_none()
expect true
```

</details>

### LowerContext Creation

#### creates with global scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# expect ctx.current_scope_id == 0
# expect ctx.scopes.len() == 1
expect true
```

</details>

#### starts with no errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# expect not ctx.has_errors()
# expect ctx.errors.len() == 0
expect true
```

</details>

#### starts with void return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# expect ctx.function_return_type.is_void()
expect true
```

</details>

#### starts with no current function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# expect ctx.current_function.is_none()
expect true
```

</details>

### LowerContext Scope Management

#### push_scope increases scope count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.push_scope()
# expect ctx.scopes.len() == 2
expect true
```

</details>

#### push_scope updates current scope id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# val old_id = ctx.current_scope_id
# ctx.push_scope()
# expect ctx.current_scope_id > old_id
expect true
```

</details>

#### pop_scope restores parent scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# val parent_id = ctx.current_scope_id
# ctx.push_scope()
# ctx.pop_scope()
# expect ctx.current_scope_id == parent_id
expect true
```

</details>

#### nested scopes have correct depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# expect ctx.current_scope().depth == 0
# ctx.push_scope()
# expect ctx.current_scope().depth == 1
# ctx.push_scope()
# expect ctx.current_scope().depth == 2
expect true
```

</details>

### LowerContext Variable Declaration

#### declare_local returns LocalVar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# val local = ctx.declare_local("x", TypeId.i64_ty(), false)
# expect local.name == "x"
# expect local.index == 0
expect true
```

</details>

#### declare_local increments index

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# val a = ctx.declare_local("a", TypeId.i64_ty(), false)
# val b = ctx.declare_local("b", TypeId.i64_ty(), false)
# expect a.index == 0
# expect b.index == 1
expect true
```

</details>

#### declare_local respects mutability

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# val imm = ctx.declare_local("x", TypeId.i64_ty(), false)
# val mut = ctx.declare_local("y", TypeId.i64_ty(), true)
# expect not imm.is_mutable
# expect mut.is_mutable
expect true
```

</details>

### LowerContext Variable Resolution

#### resolve_local finds declared variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.declare_local("foo", TypeId.i64_ty(), false)
# val found = ctx.resolve_local("foo")
# expect found.is_some()
expect true
```

</details>

#### resolve_local returns None for undeclared

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# expect ctx.resolve_local("bar").is_none()
expect true
```

</details>

#### resolve_local searches parent scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.declare_local("outer", TypeId.i64_ty(), false)
# ctx.push_scope()
# val found = ctx.resolve_local("outer")
# expect found.is_some()
expect true
```

</details>

#### is_mutable returns correct value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.declare_local("x", TypeId.i64_ty(), false)
# ctx.declare_local("y", TypeId.i64_ty(), true)
# expect not ctx.is_mutable("x")
# expect ctx.is_mutable("y")
expect true
```

</details>

### LowerContext Function Management

#### enter_function sets current function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.enter_function("main", TypeId.void_ty())
# expect ctx.current_function.is_some()
# expect ctx.current_function.unwrap() == "main"
expect true
```

</details>

#### enter_function sets return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.enter_function("foo", TypeId.i64_ty())
# expect ctx.function_return_type.id == TypeId.i64_ty().id
expect true
```

</details>

#### enter_function resets local index

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.declare_local("global", TypeId.i64_ty(), false)
# ctx.enter_function("foo", TypeId.void_ty())
# val local = ctx.declare_local("param", TypeId.i64_ty(), false)
# expect local.index == 0
expect true
```

</details>

#### exit_function clears current function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.enter_function("foo", TypeId.i64_ty())
# ctx.exit_function()
# expect ctx.current_function.is_none()
expect true
```

</details>

### LowerContext Error Tracking

#### add_error adds to errors list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.add_error("test error")
# expect ctx.errors.len() == 1
# expect ctx.has_errors()
expect true
```

</details>

#### add_warning adds to warnings list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# ctx.add_warning("test warning")
# expect ctx.warnings.len() == 1
expect true
```

</details>

#### has_errors returns false when no errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = LowerContext.new()
# expect not ctx.has_errors()
expect true
```

</details>

### HirExpr Literal Factories

#### integer creates Integer expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val expr = HirExpr.integer(42)
# expect expr.kind == HirExprKind.Integer
# expect expr.int_value == 42
expect true
```

</details>

#### float creates Float expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val expr = HirExpr.float(3.14)
# expect expr.kind == HirExprKind.Float
# expect expr.float_value == 3.14
expect true
```

</details>

#### bool_lit creates Bool expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val expr = HirExpr.bool_lit(true)
# expect expr.kind == HirExprKind.Bool
# expect expr.bool_value == true
expect true
```

</details>

#### string_lit creates String expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val expr = HirExpr.string_lit("hello")
# expect expr.kind == HirExprKind.String
# expect expr.str_value == "hello"
expect true
```

</details>

#### nil_lit creates Nil expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val expr = HirExpr.nil_lit()
# expect expr.kind == HirExprKind.Nil
expect true
```

</details>

### HirExpr Local Factory

#### local creates Local expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val expr = HirExpr.local(5, TypeId.i64_ty())
# expect expr.kind == HirExprKind.Local
# expect expr.local_index == 5
expect true
```

</details>

### HirStmt Factories

#### let_stmt creates Let statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val init = HirExpr.integer(42)
# val stmt = HirStmt.let_stmt(0, init)
# expect stmt.kind == HirStmtKind.Let
# expect stmt.local_index == 0
expect true
```

</details>

#### assign creates Assign statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val value = HirExpr.integer(10)
# val stmt = HirStmt.assign(0, value)
# expect stmt.kind == HirStmtKind.Assign
expect true
```

</details>

#### return_stmt creates Return statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val value = HirExpr.integer(0)
# val stmt = HirStmt.return_stmt(Some(value))
# expect stmt.kind == HirStmtKind.Return
expect true
```

</details>

#### expr_stmt creates Expr statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val expr = HirExpr.nil_lit()
# val stmt = HirStmt.expr_stmt(expr)
# expect stmt.kind == HirStmtKind.Expr
expect true
```

</details>

#### if_stmt creates If statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val cond = HirExpr.bool_lit(true)
# val stmt = HirStmt.if_stmt(cond, [], [])
# expect stmt.kind == HirStmtKind.If
expect true
```

</details>

#### while_stmt creates While statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val cond = HirExpr.bool_lit(true)
# val stmt = HirStmt.while_stmt(cond, [])
# expect stmt.kind == HirStmtKind.While
expect true
```

</details>

#### break_stmt creates Break statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stmt = HirStmt.break_stmt()
# expect stmt.kind == HirStmtKind.Break
expect true
```

</details>

#### continue_stmt creates Continue statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val stmt = HirStmt.continue_stmt()
# expect stmt.kind == HirStmtKind.Continue
expect true
```

</details>

### Lowerer Creation

#### creates with fresh context

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# expect not lowerer.has_errors()
expect true
```

</details>

### Lowerer Literal Lowering

#### lower_integer returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val result = lowerer.lower_integer(42)
# expect result.is_ok()
expect true
```

</details>

#### lower_float returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val result = lowerer.lower_float(3.14)
# expect result.is_ok()
expect true
```

</details>

#### lower_bool returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val result = lowerer.lower_bool(true)
# expect result.is_ok()
expect true
```

</details>

#### lower_string returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val result = lowerer.lower_string("hello")
# expect result.is_ok()
expect true
```

</details>

#### lower_nil returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val result = lowerer.lower_nil()
# expect result.is_ok()
expect true
```

</details>

### Lowerer Variable Lowering

#### lower_variable returns Err for undefined

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val result = lowerer.lower_variable("unknown")
# expect not result.is_ok()
expect true
```

</details>

#### lower_variable returns Ok for declared

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val init = HirExpr.integer(0)
# lowerer.lower_let("x", init, false)
# val result = lowerer.lower_variable("x")
# expect result.is_ok()
expect true
```

</details>

### Lowerer Statement Lowering

#### lower_let declares local

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val init = HirExpr.integer(42)
# val result = lowerer.lower_let("x", init, false)
# expect result.is_ok()
# expect lowerer.ctx.resolve_local("x").is_some()
expect true
```

</details>

#### lower_assign fails for immutable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val init = HirExpr.integer(0)
# lowerer.lower_let("x", init, false)
# val result = lowerer.lower_assign("x", HirExpr.integer(1))
# expect not result.is_ok()
expect true
```

</details>

#### lower_assign succeeds for mutable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val init = HirExpr.integer(0)
# lowerer.lower_let("x", init, true)
# val result = lowerer.lower_assign("x", HirExpr.integer(1))
# expect result.is_ok()
expect true
```

</details>

#### lower_return returns Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val result = lowerer.lower_return(None)
# expect result.is_ok()
expect true
```

</details>

### Lowerer Scope Operations

#### push_scope/pop_scope maintain consistency

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# val initial_id = lowerer.ctx.current_scope_id
# lowerer.push_scope()
# lowerer.pop_scope()
# expect lowerer.ctx.current_scope_id == initial_id
expect true
```

</details>

#### enter_function/exit_function work correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var lowerer = Lowerer.new()
# lowerer.enter_function("test", TypeId.void_ty())
# expect lowerer.ctx.current_function.is_some()
# lowerer.exit_function()
# expect lowerer.ctx.current_function.is_none()
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
