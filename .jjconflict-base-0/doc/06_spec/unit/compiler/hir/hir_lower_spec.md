# Hir Lower Specification

> Tests covering Scope Creation, Scope Local Variables, LowerContext Creation, LowerContext Scope Management, LowerContext Variable Declaration, LowerContext Variable Resolution, LowerContext Function Management, LowerContext Error Tracking, HirExpr Literal Factories, HirExpr Local Factory, HirStmt Factories, Lowerer Creation, Lowerer Literal Lowering, Lowerer Variable Lowering, Lowerer Statement Lowering, Lowerer Scope Operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Lower Specification

## Scenarios

### Scope Creation

#### creates scope with parent id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates scope with parent id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates scope with parent id")
# val scope = Scope.new(-1, 0)
# expect scope.parent_scope_id == -1
# expect scope.depth == 0
expect true
```

</details>

#### creates nested scope

- creates nested scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates nested scope")
# val parent = Scope.new(-1, 0)
# val child = Scope.new(0, 1)
# expect child.parent_scope_id == 0
# expect child.depth == 1
expect true
```

</details>

#### starts with no locals

- starts with no locals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with no locals")
# val scope = Scope.new(-1, 0)
# expect scope.local_count() == 0
expect true
```

</details>

### Scope Local Variables

#### add_local increases count

- add_local increases count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_local increases count")
# var scope = Scope.new(-1, 0)
# val local = LocalVar.new("x", TypeId.i64_ty(), false, 0)
# scope.add_local(local)
# expect scope.local_count() == 1
expect true
```

</details>

#### find_local finds added local

- find_local finds added local


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_local finds added local")
# var scope = Scope.new(-1, 0)
# scope.add_local(LocalVar.new("foo", TypeId.i64_ty(), false, 0))
# val found = scope.find_local("foo")
# expect found.is_some()
# expect found.unwrap().name == "foo"
expect true
```

</details>

#### find_local returns None for unknown

- find_local returns None for unknown


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_local returns None for unknown")
# val scope = Scope.new(-1, 0)
# expect scope.find_local("bar").is_none()
expect true
```

</details>

### LowerContext Creation

#### creates with global scope

- creates with global scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with global scope")
# var ctx = LowerContext.new()
# expect ctx.current_scope_id == 0
# expect ctx.scopes.len() == 1
expect true
```

</details>

#### starts with no errors

- starts with no errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with no errors")
# var ctx = LowerContext.new()
# expect not ctx.has_errors()
# expect ctx.errors.len() == 0
expect true
```

</details>

#### starts with void return type

- starts with void return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with void return type")
# var ctx = LowerContext.new()
# expect ctx.function_return_type.is_void()
expect true
```

</details>

#### starts with no current function

- starts with no current function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with no current function")
# var ctx = LowerContext.new()
# expect ctx.current_function.is_none()
expect true
```

</details>

### LowerContext Scope Management

#### push_scope increases scope count

- push_scope increases scope count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_scope increases scope count")
# var ctx = LowerContext.new()
# ctx.push_scope()
# expect ctx.scopes.len() == 2
expect true
```

</details>

#### push_scope updates current scope id

- push_scope updates current scope id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_scope updates current scope id")
# var ctx = LowerContext.new()
# val old_id = ctx.current_scope_id
# ctx.push_scope()
# expect ctx.current_scope_id > old_id
expect true
```

</details>

#### pop_scope restores parent scope

- pop_scope restores parent scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pop_scope restores parent scope")
# var ctx = LowerContext.new()
# val parent_id = ctx.current_scope_id
# ctx.push_scope()
# ctx.pop_scope()
# expect ctx.current_scope_id == parent_id
expect true
```

</details>

#### nested scopes have correct depth

- nested scopes have correct depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested scopes have correct depth")
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

- declare_local returns LocalVar


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declare_local returns LocalVar")
# var ctx = LowerContext.new()
# val local = ctx.declare_local("x", TypeId.i64_ty(), false)
# expect local.name == "x"
# expect local.index == 0
expect true
```

</details>

#### declare_local increments index

- declare_local increments index


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declare_local increments index")
# var ctx = LowerContext.new()
# val a = ctx.declare_local("a", TypeId.i64_ty(), false)
# val b = ctx.declare_local("b", TypeId.i64_ty(), false)
# expect a.index == 0
# expect b.index == 1
expect true
```

</details>

#### declare_local respects mutability

- declare_local respects mutability


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declare_local respects mutability")
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

- resolve_local finds declared variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve_local finds declared variable")
# var ctx = LowerContext.new()
# ctx.declare_local("foo", TypeId.i64_ty(), false)
# val found = ctx.resolve_local("foo")
# expect found.is_some()
expect true
```

</details>

#### resolve_local returns None for undeclared

- resolve_local returns None for undeclared


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve_local returns None for undeclared")
# var ctx = LowerContext.new()
# expect ctx.resolve_local("bar").is_none()
expect true
```

</details>

#### resolve_local searches parent scope

- resolve_local searches parent scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolve_local searches parent scope")
# var ctx = LowerContext.new()
# ctx.declare_local("outer", TypeId.i64_ty(), false)
# ctx.push_scope()
# val found = ctx.resolve_local("outer")
# expect found.is_some()
expect true
```

</details>

#### is_mutable returns correct value

- is_mutable returns correct value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_mutable returns correct value")
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

- enter_function sets current function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enter_function sets current function")
# var ctx = LowerContext.new()
# ctx.enter_function("main", TypeId.void_ty())
# expect ctx.current_function.is_some()
# expect ctx.current_function.unwrap() == "main"
expect true
```

</details>

#### enter_function sets return type

- enter_function sets return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enter_function sets return type")
# var ctx = LowerContext.new()
# ctx.enter_function("foo", TypeId.i64_ty())
# expect ctx.function_return_type.id == TypeId.i64_ty().id
expect true
```

</details>

#### enter_function resets local index

- enter_function resets local index


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enter_function resets local index")
# var ctx = LowerContext.new()
# ctx.declare_local("global", TypeId.i64_ty(), false)
# ctx.enter_function("foo", TypeId.void_ty())
# val local = ctx.declare_local("param", TypeId.i64_ty(), false)
# expect local.index == 0
expect true
```

</details>

#### exit_function clears current function

- exit_function clears current function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exit_function clears current function")
# var ctx = LowerContext.new()
# ctx.enter_function("foo", TypeId.i64_ty())
# ctx.exit_function()
# expect ctx.current_function.is_none()
expect true
```

</details>

### LowerContext Error Tracking

#### add_error adds to errors list

- add_error adds to errors list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_error adds to errors list")
# var ctx = LowerContext.new()
# ctx.add_error("test error")
# expect ctx.errors.len() == 1
# expect ctx.has_errors()
expect true
```

</details>

#### add_warning adds to warnings list

- add_warning adds to warnings list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_warning adds to warnings list")
# var ctx = LowerContext.new()
# ctx.add_warning("test warning")
# expect ctx.warnings.len() == 1
expect true
```

</details>

#### has_errors returns false when no errors

- has_errors returns false when no errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_errors returns false when no errors")
# var ctx = LowerContext.new()
# expect not ctx.has_errors()
expect true
```

</details>

### HirExpr Literal Factories

#### integer creates Integer expression

- integer creates Integer expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer creates Integer expression")
# val expr = HirExpr.integer(42)
# expect expr.kind == HirExprKind.Integer
# expect expr.int_value == 42
expect true
```

</details>

#### float creates Float expression

- float creates Float expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float creates Float expression")
# val expr = HirExpr.float(3.14)
# expect expr.kind == HirExprKind.Float
# expect expr.float_value == 3.14
expect true
```

</details>

#### bool_lit creates Bool expression

- bool_lit creates Bool expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool_lit creates Bool expression")
# val expr = HirExpr.bool_lit(true)
# expect expr.kind == HirExprKind.Bool
# expect expr.bool_value == true
expect true
```

</details>

#### string_lit creates String expression

- string_lit creates String expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string_lit creates String expression")
# val expr = HirExpr.string_lit("hello")
# expect expr.kind == HirExprKind.String
# expect expr.str_value == "hello"
expect true
```

</details>

#### nil_lit creates Nil expression

- nil_lit creates Nil expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil_lit creates Nil expression")
# val expr = HirExpr.nil_lit()
# expect expr.kind == HirExprKind.Nil
expect true
```

</details>

### HirExpr Local Factory

#### local creates Local expression

- local creates Local expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local creates Local expression")
# val expr = HirExpr.local(5, TypeId.i64_ty())
# expect expr.kind == HirExprKind.Local
# expect expr.local_index == 5
expect true
```

</details>

### HirStmt Factories

#### let_stmt creates Let statement

- let_stmt creates Let statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("let_stmt creates Let statement")
# val init = HirExpr.integer(42)
# val stmt = HirStmt.let_stmt(0, init)
# expect stmt.kind == HirStmtKind.Let
# expect stmt.local_index == 0
expect true
```

</details>

#### assign creates Assign statement

- assign creates Assign statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assign creates Assign statement")
# val value = HirExpr.integer(10)
# val stmt = HirStmt.assign(0, value)
# expect stmt.kind == HirStmtKind.Assign
expect true
```

</details>

#### return_stmt creates Return statement

- return_stmt creates Return statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("return_stmt creates Return statement")
# val value = HirExpr.integer(0)
# val stmt = HirStmt.return_stmt(Some(value))
# expect stmt.kind == HirStmtKind.Return
expect true
```

</details>

#### expr_stmt creates Expr statement

- expr_stmt creates Expr statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expr_stmt creates Expr statement")
# val expr = HirExpr.nil_lit()
# val stmt = HirStmt.expr_stmt(expr)
# expect stmt.kind == HirStmtKind.Expr
expect true
```

</details>

#### if_stmt creates If statement

- if_stmt creates If statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if_stmt creates If statement")
# val cond = HirExpr.bool_lit(true)
# val stmt = HirStmt.if_stmt(cond, [], [])
# expect stmt.kind == HirStmtKind.If
expect true
```

</details>

#### while_stmt creates While statement

- while_stmt creates While statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while_stmt creates While statement")
# val cond = HirExpr.bool_lit(true)
# val stmt = HirStmt.while_stmt(cond, [])
# expect stmt.kind == HirStmtKind.While
expect true
```

</details>

#### break_stmt creates Break statement

- break_stmt creates Break statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("break_stmt creates Break statement")
# val stmt = HirStmt.break_stmt()
# expect stmt.kind == HirStmtKind.Break
expect true
```

</details>

#### continue_stmt creates Continue statement

- continue_stmt creates Continue statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continue_stmt creates Continue statement")
# val stmt = HirStmt.continue_stmt()
# expect stmt.kind == HirStmtKind.Continue
expect true
```

</details>

### Lowerer Creation

#### creates with fresh context

- creates with fresh context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with fresh context")
# var lowerer = Lowerer.new()
# expect not lowerer.has_errors()
expect true
```

</details>

### Lowerer Literal Lowering

#### lower_integer returns Ok

- lower_integer returns Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_integer returns Ok")
# var lowerer = Lowerer.new()
# val result = lowerer.lower_integer(42)
# expect result.is_ok()
expect true
```

</details>

#### lower_float returns Ok

- lower_float returns Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_float returns Ok")
# var lowerer = Lowerer.new()
# val result = lowerer.lower_float(3.14)
# expect result.is_ok()
expect true
```

</details>

#### lower_bool returns Ok

- lower_bool returns Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_bool returns Ok")
# var lowerer = Lowerer.new()
# val result = lowerer.lower_bool(true)
# expect result.is_ok()
expect true
```

</details>

#### lower_string returns Ok

- lower_string returns Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_string returns Ok")
# var lowerer = Lowerer.new()
# val result = lowerer.lower_string("hello")
# expect result.is_ok()
expect true
```

</details>

#### lower_nil returns Ok

- lower_nil returns Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_nil returns Ok")
# var lowerer = Lowerer.new()
# val result = lowerer.lower_nil()
# expect result.is_ok()
expect true
```

</details>

### Lowerer Variable Lowering

#### lower_variable returns Err for undefined

- lower_variable returns Err for undefined


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_variable returns Err for undefined")
# var lowerer = Lowerer.new()
# val result = lowerer.lower_variable("unknown")
# expect not result.is_ok()
expect true
```

</details>

#### lower_variable returns Ok for declared

- lower_variable returns Ok for declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_variable returns Ok for declared")
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

- lower_let declares local


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_let declares local")
# var lowerer = Lowerer.new()
# val init = HirExpr.integer(42)
# val result = lowerer.lower_let("x", init, false)
# expect result.is_ok()
# expect lowerer.ctx.resolve_local("x").is_some()
expect true
```

</details>

#### lower_assign fails for immutable

- lower_assign fails for immutable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_assign fails for immutable")
# var lowerer = Lowerer.new()
# val init = HirExpr.integer(0)
# lowerer.lower_let("x", init, false)
# val result = lowerer.lower_assign("x", HirExpr.integer(1))
# expect not result.is_ok()
expect true
```

</details>

#### lower_assign succeeds for mutable

- lower_assign succeeds for mutable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_assign succeeds for mutable")
# var lowerer = Lowerer.new()
# val init = HirExpr.integer(0)
# lowerer.lower_let("x", init, true)
# val result = lowerer.lower_assign("x", HirExpr.integer(1))
# expect result.is_ok()
expect true
```

</details>

#### lower_return returns Ok

- lower_return returns Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower_return returns Ok")
# var lowerer = Lowerer.new()
# val result = lowerer.lower_return(None)
# expect result.is_ok()
expect true
```

</details>

### Lowerer Scope Operations

#### push_scope/pop_scope maintain consistency

- push_scope/pop_scope maintain consistency


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_scope/pop_scope maintain consistency")
# var lowerer = Lowerer.new()
# val initial_id = lowerer.ctx.current_scope_id
# lowerer.push_scope()
# lowerer.pop_scope()
# expect lowerer.ctx.current_scope_id == initial_id
expect true
```

</details>

#### enter_function/exit_function work correctly

- enter_function/exit_function work correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enter_function/exit_function work correctly")
# var lowerer = Lowerer.new()
# lowerer.enter_function("test", TypeId.void_ty())
# expect lowerer.ctx.current_function.is_some()
# lowerer.exit_function()
# expect lowerer.ctx.current_function.is_none()
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/hir_lower_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Scope Creation, Scope Local Variables, LowerContext Creation, LowerContext Scope Management, LowerContext Variable Declaration, LowerContext Variable Resolution, LowerContext Function Management, LowerContext Error Tracking, HirExpr Literal Factories, HirExpr Local Factory, HirStmt Factories, Lowerer Creation, Lowerer Literal Lowering, Lowerer Variable Lowering, Lowerer Statement Lowering, Lowerer Scope Operations.
- Scope Creation
- Scope Local Variables
- LowerContext Creation
- LowerContext Scope Management
- LowerContext Variable Declaration
- LowerContext Variable Resolution
- LowerContext Function Management
- LowerContext Error Tracking
- HirExpr Literal Factories
- HirExpr Local Factory
- HirStmt Factories
- Lowerer Creation
- Lowerer Literal Lowering
- Lowerer Variable Lowering
- Lowerer Statement Lowering
- Lowerer Scope Operations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
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

- Canonical SPipe generation for source `534f7c1121777755c03e5d8c8e53d7fd7a9ab20b98ccc1d0dbb2a27e35f258d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `534f7c1121777755c03e5d8c8e53d7fd7a9ab20b98ccc1d0dbb2a27e35f258d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `534f7c1121777755c03e5d8c8e53d7fd7a9ab20b98ccc1d0dbb2a27e35f258d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/hir/hir_lower_spec.spl
mirror: doc/06_spec/unit/compiler/hir/hir_lower_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/hir_lower_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/hir_lower_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/hir_lower_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates scope with parent id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/hir_lower_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates nested scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/hir_lower_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with no locals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
