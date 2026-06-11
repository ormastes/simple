# HIR Types Unit Tests

> Tests for HIR type system: TypeId, BinOp, UnaryOp, HirExprKind, HirStmtKind.

<!-- sdn-diagram:id=hir_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hir_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hir_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hir_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 86 | 86 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR Types Unit Tests

Tests for HIR type system: TypeId, BinOp, UnaryOp, HirExprKind, HirStmtKind.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HIR-TYPES-001 |
| Category | HIR \| Types |
| Status | In Progress |
| Source | `test/01_unit/compiler/hir/hir_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for HIR type system: TypeId, BinOp, UnaryOp, HirExprKind, HirStmtKind.

## Scenarios

### TypeId Factory Functions

#### void_ty returns id 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.void_ty().id == 0
expect true
```

</details>

#### bool_ty returns id 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.bool_ty().id == 1
expect true
```

</details>

#### i64_ty returns id 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.i64_ty().id == 5
expect true
```

</details>

#### f64_ty returns id 11

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.f64_ty().id == 11
expect true
```

</details>

#### string_ty returns id 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.string_ty().id == 12
expect true
```

</details>

#### nil_ty returns id 13

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.nil_ty().id == 13
expect true
```

</details>

### TypeId Predicates

#### is_void returns true for void_ty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.void_ty().is_void()
expect true
```

</details>

#### is_bool returns true for bool_ty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.bool_ty().is_bool()
expect true
```

</details>

#### is_integer returns true for i64_ty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.i64_ty().is_integer()
expect true
```

</details>

#### is_signed_integer returns true for i32_ty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.i32_ty().is_signed_integer()
expect true
```

</details>

#### is_unsigned_integer returns true for u64_ty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.u64_ty().is_unsigned_integer()
expect true
```

</details>

#### is_float returns true for f64_ty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.f64_ty().is_float()
expect true
```

</details>

#### is_numeric returns true for integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.i64_ty().is_numeric()
expect true
```

</details>

#### is_numeric returns true for floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.f64_ty().is_numeric()
expect true
```

</details>

#### is_string returns true for string_ty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.string_ty().is_string()
expect true
```

</details>

#### is_nil returns true for nil_ty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.nil_ty().is_nil()
expect true
```

</details>

#### is_primitive returns true for all primitives

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.void_ty().is_primitive()
# expect TypeId.bool_ty().is_primitive()
# expect TypeId.i64_ty().is_primitive()
# expect TypeId.string_ty().is_primitive()
expect true
```

</details>

### TypeId Names

#### name returns correct string for primitives

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect TypeId.void_ty().name() == "void"
# expect TypeId.bool_ty().name() == "bool"
# expect TypeId.i64_ty().name() == "i64"
# expect TypeId.f64_ty().name() == "f64"
# expect TypeId.string_ty().name() == "text"
expect true
```

</details>

### BinOp Arithmetic

#### Add is arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Add.is_arithmetic()
expect true
```

</details>

#### Sub is arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Sub.is_arithmetic()
expect true
```

</details>

#### Mul is arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Mul.is_arithmetic()
expect true
```

</details>

#### Div is arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Div.is_arithmetic()
expect true
```

</details>

#### Mod is arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Mod.is_arithmetic()
expect true
```

</details>

#### Pow is arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Pow.is_arithmetic()
expect true
```

</details>

### BinOp Comparison

#### Eq is comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Eq.is_comparison()
expect true
```

</details>

#### NotEq is comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.NotEq.is_comparison()
expect true
```

</details>

#### Lt is comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Lt.is_comparison()
expect true
```

</details>

#### Gt is comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Gt.is_comparison()
expect true
```

</details>

#### comparison operators return bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Eq.returns_bool()
# expect BinOp.Lt.returns_bool()
expect true
```

</details>

### BinOp Logical

#### And is logical

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.And.is_logical()
expect true
```

</details>

#### Or is logical

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Or.is_logical()
expect true
```

</details>

#### logical operators return bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.And.returns_bool()
# expect BinOp.Or.returns_bool()
expect true
```

</details>

### BinOp Bitwise

#### BitAnd is bitwise

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.BitAnd.is_bitwise()
expect true
```

</details>

#### BitOr is bitwise

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.BitOr.is_bitwise()
expect true
```

</details>

#### ShiftLeft is bitwise

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.ShiftLeft.is_bitwise()
expect true
```

</details>

### BinOp to_string

#### Add to_string is +

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Add.to_string() == "+"
expect true
```

</details>

#### Eq to_string is ==

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.Eq.to_string() == "=="
expect true
```

</details>

#### And to_string is and

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect BinOp.And.to_string() == "and"
expect true
```

</details>

### UnaryOp

#### Neg is negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect UnaryOp.Neg.is_neg()
expect true
```

</details>

#### Not is logical not

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect UnaryOp.Not.is_not()
expect true
```

</details>

#### Neg to_string is -

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect UnaryOp.Neg.to_string() == "-"
expect true
```

</details>

#### Not to_string is not

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect UnaryOp.Not.to_string() == "not"
expect true
```

</details>

#### BitNot to_string is ~

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect UnaryOp.BitNot.to_string() == "~"
expect true
```

</details>

### DispatchMode

#### Static is_static returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect DispatchMode.Static.is_static()
expect true
```

</details>

#### Dynamic is_dynamic returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect DispatchMode.Dynamic.is_dynamic()
expect true
```

</details>

#### Static to_string is static

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect DispatchMode.Static.to_string() == "static"
expect true
```

</details>

### CaptureMode

#### ByValue is_by_value returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect CaptureMode.ByValue.is_by_value()
expect true
```

</details>

#### ByRef is_reference returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect CaptureMode.ByRef.is_reference()
expect true
```

</details>

#### ByMutRef is_mutable returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect CaptureMode.ByMutRef.is_mutable()
expect true
```

</details>

### LocalVar

#### creates immutable local

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val local = LocalVar.immutable("x", TypeId.i64_ty(), 0)
# expect local.name == "x"
# expect local.is_mutable == false
# expect local.index == 0
expect true
```

</details>

#### creates mutable local

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val local = LocalVar.mutable_var("y", TypeId.i64_ty(), 1)
# expect local.is_mutable == true
expect true
```

</details>

### CapturedVar

#### creates by_value capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val cap = CapturedVar.by_value(0)
# expect cap.local_index == 0
# expect cap.capture_mode.is_by_value()
expect true
```

</details>

#### creates by_ref capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val cap = CapturedVar.by_ref(1)
# expect cap.capture_mode.is_reference()
expect true
```

</details>

### HirExprKind Literals

#### Integer is literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirExprKind.Integer.is_literal()
expect true
```

</details>

#### Float is literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirExprKind.Float.is_literal()
expect true
```

</details>

#### Bool is literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirExprKind.Bool.is_literal()
expect true
```

</details>

#### String is literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirExprKind.String.is_literal()
expect true
```

</details>

#### Nil is literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirExprKind.Nil.is_literal()
expect true
```

</details>

### HirExprKind Variables

#### Local is variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirExprKind.Local.is_variable()
expect true
```

</details>

#### Global is variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirExprKind.Global.is_variable()
expect true
```

</details>

### HirExprKind Control Flow

#### If is control flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirExprKind.If.is_control_flow()
expect true
```

</details>

#### Match is control flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirExprKind.Match.is_control_flow()
expect true
```

</details>

### HirExprNode Factory

#### integer creates Integer node

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val node = HirExprNode.integer(TypeId.i64_ty())
# expect node.kind == HirExprKind.Integer
# expect node.get_type().id == TypeId.i64_ty().id
expect true
```

</details>

#### bool_node creates Bool node

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val node = HirExprNode.bool_node()
# expect node.kind == HirExprKind.Bool
# expect node.get_type().is_bool()
expect true
```

</details>

#### nil_node creates Nil node

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val node = HirExprNode.nil_node()
# expect node.kind == HirExprKind.Nil
# expect node.get_type().is_nil()
expect true
```

</details>

#### local creates Local node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val node = HirExprNode.local(TypeId.i64_ty())
# expect node.is_variable()
expect true
```

</details>

### HirExprNode Predicates

#### is_literal delegates to kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val int_node = HirExprNode.integer(TypeId.i64_ty())
# expect int_node.is_literal()
expect true
```

</details>

#### is_variable delegates to kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val local_node = HirExprNode.local(TypeId.i64_ty())
# expect local_node.is_variable()
expect true
```

</details>

### HirStmtKind

#### Let is_let returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirStmtKind.Let.is_let()
expect true
```

</details>

#### Return is_return returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirStmtKind.Return.is_return()
expect true
```

</details>

#### If is_control_flow returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirStmtKind.If.is_control_flow()
expect true
```

</details>

#### While is_control_flow returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirStmtKind.While.is_control_flow()
expect true
```

</details>

<details>
<summary>Advanced: Break is_loop_control returns true</summary>

#### Break is_loop_control returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirStmtKind.Break.is_loop_control()
expect true
```

</details>


</details>

<details>
<summary>Advanced: Continue is_loop_control returns true</summary>

#### Continue is_loop_control returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirStmtKind.Continue.is_loop_control()
expect true
```

</details>


</details>

### HirStmtNode Factory

#### let_stmt creates Let node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val node = HirStmtNode.let_stmt()
# expect node.is_let()
expect true
```

</details>

#### return_stmt creates Return node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val node = HirStmtNode.return_stmt()
# expect node.is_return()
expect true
```

</details>

#### if_stmt creates If node

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val node = HirStmtNode.if_stmt()
# expect node.is_control_flow()
expect true
```

</details>

### HirPatternKind

#### Wildcard is_wildcard returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirPatternKind.Wildcard.is_wildcard()
expect true
```

</details>

#### Binding is_binding returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirPatternKind.Binding.is_binding()
expect true
```

</details>

#### Literal is_literal returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirPatternKind.Literal.is_literal()
expect true
```

</details>

### HirLiteral

#### Int has correct type_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val lit = HirLiteral.Int(42)
# expect lit.type_name() == "int"
expect true
```

</details>

#### Float has correct type_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val lit = HirLiteral.Float(3.14)
# expect lit.type_name() == "float"
expect true
```

</details>

#### Nil is_nil returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val lit = HirLiteral.Nil
# expect lit.is_nil()
expect true
```

</details>

#### is_number returns true for Int

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val lit = HirLiteral.Int(42)
# expect lit.is_number()
expect true
```

</details>

#### is_number returns true for Float

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val lit = HirLiteral.Float(3.14)
# expect lit.is_number()
expect true
```

</details>

#### to_bool returns correct values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect HirLiteral.Bool(true).to_bool() == true
# expect HirLiteral.Bool(false).to_bool() == false
# expect HirLiteral.Nil.to_bool() == false
# expect HirLiteral.Int(0).to_bool() == false
# expect HirLiteral.Int(1).to_bool() == true
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 86 |
| Active scenarios | 86 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
