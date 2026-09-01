# Hir Types Specification

> Tests covering TypeId Factory Functions, TypeId Predicates, TypeId Names, BinOp Arithmetic, BinOp Comparison, BinOp Logical, BinOp Bitwise, BinOp to_string, UnaryOp, DispatchMode, CaptureMode, LocalVar, CapturedVar, HirExprKind Literals, HirExprKind Variables, HirExprKind Control Flow, HirExprNode Factory, HirExprNode Predicates, HirStmtKind, HirStmtNode Factory, HirPatternKind, HirLiteral.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 86 | 86 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Types Specification

## Scenarios

### TypeId Factory Functions

#### void_ty returns id 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- void_ty returns id 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("void_ty returns id 0")
# expect TypeId.void_ty().id == 0
expect true
```

</details>

#### bool_ty returns id 1

- bool_ty returns id 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool_ty returns id 1")
# expect TypeId.bool_ty().id == 1
expect true
```

</details>

#### i64_ty returns id 5

- i64_ty returns id 5


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i64_ty returns id 5")
# expect TypeId.i64_ty().id == 5
expect true
```

</details>

#### f64_ty returns id 11

- f64_ty returns id 11


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f64_ty returns id 11")
# expect TypeId.f64_ty().id == 11
expect true
```

</details>

#### string_ty returns id 12

- string_ty returns id 12


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string_ty returns id 12")
# expect TypeId.string_ty().id == 12
expect true
```

</details>

#### nil_ty returns id 13

- nil_ty returns id 13


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil_ty returns id 13")
# expect TypeId.nil_ty().id == 13
expect true
```

</details>

### TypeId Predicates

#### is_void returns true for void_ty

- is_void returns true for void_ty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_void returns true for void_ty")
# expect TypeId.void_ty().is_void()
expect true
```

</details>

#### is_bool returns true for bool_ty

- is_bool returns true for bool_ty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_bool returns true for bool_ty")
# expect TypeId.bool_ty().is_bool()
expect true
```

</details>

#### is_integer returns true for i64_ty

- is_integer returns true for i64_ty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_integer returns true for i64_ty")
# expect TypeId.i64_ty().is_integer()
expect true
```

</details>

#### is_signed_integer returns true for i32_ty

- is_signed_integer returns true for i32_ty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_signed_integer returns true for i32_ty")
# expect TypeId.i32_ty().is_signed_integer()
expect true
```

</details>

#### is_unsigned_integer returns true for u64_ty

- is_unsigned_integer returns true for u64_ty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_unsigned_integer returns true for u64_ty")
# expect TypeId.u64_ty().is_unsigned_integer()
expect true
```

</details>

#### is_float returns true for f64_ty

- is_float returns true for f64_ty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_float returns true for f64_ty")
# expect TypeId.f64_ty().is_float()
expect true
```

</details>

#### is_numeric returns true for integers

- is_numeric returns true for integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_numeric returns true for integers")
# expect TypeId.i64_ty().is_numeric()
expect true
```

</details>

#### is_numeric returns true for floats

- is_numeric returns true for floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_numeric returns true for floats")
# expect TypeId.f64_ty().is_numeric()
expect true
```

</details>

#### is_string returns true for string_ty

- is_string returns true for string_ty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_string returns true for string_ty")
# expect TypeId.string_ty().is_string()
expect true
```

</details>

#### is_nil returns true for nil_ty

- is_nil returns true for nil_ty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_nil returns true for nil_ty")
# expect TypeId.nil_ty().is_nil()
expect true
```

</details>

#### is_primitive returns true for all primitives

- is_primitive returns true for all primitives


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_primitive returns true for all primitives")
# expect TypeId.void_ty().is_primitive()
# expect TypeId.bool_ty().is_primitive()
# expect TypeId.i64_ty().is_primitive()
# expect TypeId.string_ty().is_primitive()
expect true
```

</details>

### TypeId Names

#### name returns correct string for primitives

- name returns correct string for primitives


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("name returns correct string for primitives")
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

- Add is arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Add is arithmetic")
# expect BinOp.Add.is_arithmetic()
expect true
```

</details>

#### Sub is arithmetic

- Sub is arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sub is arithmetic")
# expect BinOp.Sub.is_arithmetic()
expect true
```

</details>

#### Mul is arithmetic

- Mul is arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Mul is arithmetic")
# expect BinOp.Mul.is_arithmetic()
expect true
```

</details>

#### Div is arithmetic

- Div is arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Div is arithmetic")
# expect BinOp.Div.is_arithmetic()
expect true
```

</details>

#### Mod is arithmetic

- Mod is arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Mod is arithmetic")
# expect BinOp.Mod.is_arithmetic()
expect true
```

</details>

#### Pow is arithmetic

- Pow is arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Pow is arithmetic")
# expect BinOp.Pow.is_arithmetic()
expect true
```

</details>

### BinOp Comparison

#### Eq is comparison

- Eq is comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Eq is comparison")
# expect BinOp.Eq.is_comparison()
expect true
```

</details>

#### NotEq is comparison

- NotEq is comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NotEq is comparison")
# expect BinOp.NotEq.is_comparison()
expect true
```

</details>

#### Lt is comparison

- Lt is comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Lt is comparison")
# expect BinOp.Lt.is_comparison()
expect true
```

</details>

#### Gt is comparison

- Gt is comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Gt is comparison")
# expect BinOp.Gt.is_comparison()
expect true
```

</details>

#### comparison operators return bool

- comparison operators return bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("comparison operators return bool")
# expect BinOp.Eq.returns_bool()
# expect BinOp.Lt.returns_bool()
expect true
```

</details>

### BinOp Logical

#### And is logical

- And is logical


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("And is logical")
# expect BinOp.And.is_logical()
expect true
```

</details>

#### Or is logical

- Or is logical


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Or is logical")
# expect BinOp.Or.is_logical()
expect true
```

</details>

#### logical operators return bool

- logical operators return bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logical operators return bool")
# expect BinOp.And.returns_bool()
# expect BinOp.Or.returns_bool()
expect true
```

</details>

### BinOp Bitwise

#### BitAnd is bitwise

- BitAnd is bitwise


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BitAnd is bitwise")
# expect BinOp.BitAnd.is_bitwise()
expect true
```

</details>

#### BitOr is bitwise

- BitOr is bitwise


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BitOr is bitwise")
# expect BinOp.BitOr.is_bitwise()
expect true
```

</details>

#### ShiftLeft is bitwise

- ShiftLeft is bitwise


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ShiftLeft is bitwise")
# expect BinOp.ShiftLeft.is_bitwise()
expect true
```

</details>

### BinOp to_string

#### Add to_string is +

- Add to_string is +


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Add to_string is +")
# expect BinOp.Add.to_string() == "+"
expect true
```

</details>

#### Eq to_string is ==

- Eq to_string is ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Eq to_string is ==")
# expect BinOp.Eq.to_string() == "=="
expect true
```

</details>

#### And to_string is and

- And to_string is and


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("And to_string is and")
# expect BinOp.And.to_string() == "and"
expect true
```

</details>

### UnaryOp

#### Neg is negation

- Neg is negation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Neg is negation")
# expect UnaryOp.Neg.is_neg()
expect true
```

</details>

#### Not is logical not

- Not is logical not


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Not is logical not")
# expect UnaryOp.Not.is_not()
expect true
```

</details>

#### Neg to_string is -

- Neg to_string is -


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Neg to_string is -")
# expect UnaryOp.Neg.to_string() == "-"
expect true
```

</details>

#### Not to_string is not

- Not to_string is not


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Not to_string is not")
# expect UnaryOp.Not.to_string() == "not"
expect true
```

</details>

#### BitNot to_string is ~

- BitNot to_string is ~


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BitNot to_string is ~")
# expect UnaryOp.BitNot.to_string() == "~"
expect true
```

</details>

### DispatchMode

#### Static is_static returns true

- Static is_static returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Static is_static returns true")
# expect DispatchMode.Static.is_static()
expect true
```

</details>

#### Dynamic is_dynamic returns true

- Dynamic is_dynamic returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Dynamic is_dynamic returns true")
# expect DispatchMode.Dynamic.is_dynamic()
expect true
```

</details>

#### Static to_string is static

- Static to_string is static


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Static to_string is static")
# expect DispatchMode.Static.to_string() == "static"
expect true
```

</details>

### CaptureMode

#### ByValue is_by_value returns true

- ByValue is_by_value returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ByValue is_by_value returns true")
# expect CaptureMode.ByValue.is_by_value()
expect true
```

</details>

#### ByRef is_reference returns true

- ByRef is_reference returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ByRef is_reference returns true")
# expect CaptureMode.ByRef.is_reference()
expect true
```

</details>

#### ByMutRef is_mutable returns true

- ByMutRef is_mutable returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ByMutRef is_mutable returns true")
# expect CaptureMode.ByMutRef.is_mutable()
expect true
```

</details>

### LocalVar

#### creates immutable local

- creates immutable local


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates immutable local")
# val local = LocalVar.immutable("x", TypeId.i64_ty(), 0)
# expect local.name == "x"
# expect local.is_mutable == false
# expect local.index == 0
expect true
```

</details>

#### creates mutable local

- creates mutable local


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates mutable local")
# val local = LocalVar.mutable_var("y", TypeId.i64_ty(), 1)
# expect local.is_mutable == true
expect true
```

</details>

### CapturedVar

#### creates by_value capture

- creates by_value capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates by_value capture")
# val cap = CapturedVar.by_value(0)
# expect cap.local_index == 0
# expect cap.capture_mode.is_by_value()
expect true
```

</details>

#### creates by_ref capture

- creates by_ref capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates by_ref capture")
# val cap = CapturedVar.by_ref(1)
# expect cap.capture_mode.is_reference()
expect true
```

</details>

### HirExprKind Literals

#### Integer is literal

- Integer is literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Integer is literal")
# expect HirExprKind.Integer.is_literal()
expect true
```

</details>

#### Float is literal

- Float is literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Float is literal")
# expect HirExprKind.Float.is_literal()
expect true
```

</details>

#### Bool is literal

- Bool is literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bool is literal")
# expect HirExprKind.Bool.is_literal()
expect true
```

</details>

#### String is literal

- String is literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("String is literal")
# expect HirExprKind.String.is_literal()
expect true
```

</details>

#### Nil is literal

- Nil is literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Nil is literal")
# expect HirExprKind.Nil.is_literal()
expect true
```

</details>

### HirExprKind Variables

#### Local is variable

- Local is variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Local is variable")
# expect HirExprKind.Local.is_variable()
expect true
```

</details>

#### Global is variable

- Global is variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Global is variable")
# expect HirExprKind.Global.is_variable()
expect true
```

</details>

### HirExprKind Control Flow

#### If is control flow

- If is control flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("If is control flow")
# expect HirExprKind.If.is_control_flow()
expect true
```

</details>

#### Match is control flow

- Match is control flow


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Match is control flow")
# expect HirExprKind.Match.is_control_flow()
expect true
```

</details>

### HirExprNode Factory

#### integer creates Integer node

- integer creates Integer node


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer creates Integer node")
# val node = HirExprNode.integer(TypeId.i64_ty())
# expect node.kind == HirExprKind.Integer
# expect node.get_type().id == TypeId.i64_ty().id
expect true
```

</details>

#### bool_node creates Bool node

- bool_node creates Bool node


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool_node creates Bool node")
# val node = HirExprNode.bool_node()
# expect node.kind == HirExprKind.Bool
# expect node.get_type().is_bool()
expect true
```

</details>

#### nil_node creates Nil node

- nil_node creates Nil node


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil_node creates Nil node")
# val node = HirExprNode.nil_node()
# expect node.kind == HirExprKind.Nil
# expect node.get_type().is_nil()
expect true
```

</details>

#### local creates Local node

- local creates Local node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local creates Local node")
# val node = HirExprNode.local(TypeId.i64_ty())
# expect node.is_variable()
expect true
```

</details>

### HirExprNode Predicates

#### is_literal delegates to kind

- is_literal delegates to kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_literal delegates to kind")
# val int_node = HirExprNode.integer(TypeId.i64_ty())
# expect int_node.is_literal()
expect true
```

</details>

#### is_variable delegates to kind

- is_variable delegates to kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_variable delegates to kind")
# val local_node = HirExprNode.local(TypeId.i64_ty())
# expect local_node.is_variable()
expect true
```

</details>

### HirStmtKind

#### Let is_let returns true

- Let is_let returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Let is_let returns true")
# expect HirStmtKind.Let.is_let()
expect true
```

</details>

#### Return is_return returns true

- Return is_return returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Return is_return returns true")
# expect HirStmtKind.Return.is_return()
expect true
```

</details>

#### If is_control_flow returns true

- If is_control_flow returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("If is_control_flow returns true")
# expect HirStmtKind.If.is_control_flow()
expect true
```

</details>

#### While is_control_flow returns true

- While is_control_flow returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("While is_control_flow returns true")
# expect HirStmtKind.While.is_control_flow()
expect true
```

</details>

<details>
<summary>Advanced: Break is_loop_control returns true</summary>

#### Break is_loop_control returns true

- Break is_loop_control returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Break is_loop_control returns true")
# expect HirStmtKind.Break.is_loop_control()
expect true
```

</details>


</details>

<details>
<summary>Advanced: Continue is_loop_control returns true</summary>

#### Continue is_loop_control returns true

- Continue is_loop_control returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Continue is_loop_control returns true")
# expect HirStmtKind.Continue.is_loop_control()
expect true
```

</details>


</details>

### HirStmtNode Factory

#### let_stmt creates Let node

- let_stmt creates Let node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("let_stmt creates Let node")
# val node = HirStmtNode.let_stmt()
# expect node.is_let()
expect true
```

</details>

#### return_stmt creates Return node

- return_stmt creates Return node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("return_stmt creates Return node")
# val node = HirStmtNode.return_stmt()
# expect node.is_return()
expect true
```

</details>

#### if_stmt creates If node

- if_stmt creates If node


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if_stmt creates If node")
# val node = HirStmtNode.if_stmt()
# expect node.is_control_flow()
expect true
```

</details>

### HirPatternKind

#### Wildcard is_wildcard returns true

- Wildcard is_wildcard returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Wildcard is_wildcard returns true")
# expect HirPatternKind.Wildcard.is_wildcard()
expect true
```

</details>

#### Binding is_binding returns true

- Binding is_binding returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Binding is_binding returns true")
# expect HirPatternKind.Binding.is_binding()
expect true
```

</details>

#### Literal is_literal returns true

- Literal is_literal returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Literal is_literal returns true")
# expect HirPatternKind.Literal.is_literal()
expect true
```

</details>

### HirLiteral

#### Int has correct type_name

- Int has correct type_name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Int has correct type_name")
# val lit = HirLiteral.Int(42)
# expect lit.type_name() == "int"
expect true
```

</details>

#### Float has correct type_name

- Float has correct type_name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Float has correct type_name")
# val lit = HirLiteral.Float(3.14)
# expect lit.type_name() == "float"
expect true
```

</details>

#### Nil is_nil returns true

- Nil is_nil returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Nil is_nil returns true")
# val lit = HirLiteral.Nil
# expect lit.is_nil()
expect true
```

</details>

#### is_number returns true for Int

- is_number returns true for Int


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_number returns true for Int")
# val lit = HirLiteral.Int(42)
# expect lit.is_number()
expect true
```

</details>

#### is_number returns true for Float

- is_number returns true for Float


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_number returns true for Float")
# val lit = HirLiteral.Float(3.14)
# expect lit.is_number()
expect true
```

</details>

#### to_bool returns correct values

- to_bool returns correct values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("to_bool returns correct values")
# expect HirLiteral.Bool(true).to_bool() == true
# expect HirLiteral.Bool(false).to_bool() == false
# expect HirLiteral.Nil.to_bool() == false
# expect HirLiteral.Int(0).to_bool() == false
# expect HirLiteral.Int(1).to_bool() == true
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/hir_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TypeId Factory Functions, TypeId Predicates, TypeId Names, BinOp Arithmetic, BinOp Comparison, BinOp Logical, BinOp Bitwise, BinOp to_string, UnaryOp, DispatchMode, CaptureMode, LocalVar, CapturedVar, HirExprKind Literals, HirExprKind Variables, HirExprKind Control Flow, HirExprNode Factory, HirExprNode Predicates, HirStmtKind, HirStmtNode Factory, HirPatternKind, HirLiteral.
- TypeId Factory Functions
- TypeId Predicates
- TypeId Names
- BinOp Arithmetic
- BinOp Comparison
- BinOp Logical
- BinOp Bitwise
- BinOp to_string
- UnaryOp
- DispatchMode
- CaptureMode
- LocalVar
- CapturedVar
- HirExprKind Literals
- HirExprKind Variables
- HirExprKind Control Flow
- HirExprNode Factory
- HirExprNode Predicates
- HirStmtKind
- HirStmtNode Factory
- HirPatternKind
- HirLiteral

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 86 |
| Active scenarios | 86 |
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

- Canonical SPipe generation for source `6fbdd76783e4820e6adb54587fd5279dc8522d23050a503581816f758800b549`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6fbdd76783e4820e6adb54587fd5279dc8522d23050a503581816f758800b549`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6fbdd76783e4820e6adb54587fd5279dc8522d23050a503581816f758800b549`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/hir/hir_types_spec.spl
mirror: doc/06_spec/unit/compiler/hir/hir_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/hir_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/hir_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/hir_types_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'void_ty returns id 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/hir_types_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bool_ty returns id 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/hir_types_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'i64_ty returns id 5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
