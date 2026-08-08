# Mir Types Specification

> <details>

<!-- sdn-diagram:id=mir_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mir_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mir_types_spec -> std
mir_types_spec -> std_lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mir_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Types Specification

## Scenarios

#### Get name of Cpu backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Cpu backend"
val backend = ParallelBackend.Cpu
# When "getting the name"
val name = backend.name()
# Then "it should return 'cpu'"
expect(name).to_equal("cpu")
```

</details>

#### Check if GPU is GPU backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Gpu backend"
val backend = ParallelBackend.Gpu
# When "checking if GPU"
val is_gpu = backend.is_gpu()
# Then "it should return true"
expect(is_gpu).to_equal(true)
```

</details>

#### Check if Simd is CPU backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Simd backend"
val backend = ParallelBackend.Simd
# When "checking if CPU"
val is_cpu = backend.is_cpu()
# Then "it should return true"
expect(is_cpu).to_equal(true)
```

</details>

#### Get name of Precondition

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Precondition contract"
val kind = ContractKind.Precondition
# When "getting the name"
val name = kind.name()
# Then "it should return 'precondition'"
expect(name).to_equal("precondition")
```

</details>

#### Check if Precondition is precondition

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Precondition contract"
val kind = ContractKind.Precondition
# When "checking if precondition"
val is_pre = kind.is_precondition()
# Then "it should return true"
expect(is_pre).to_equal(true)
```

</details>

#### Check if Postcondition is postcondition

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Postcondition contract"
val kind = ContractKind.Postcondition
# When "checking if postcondition"
val is_post = kind.is_postcondition()
# Then "it should return true"
expect(is_post).to_equal(true)
```

</details>

#### Check if InvariantEntry is invariant

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an InvariantEntry contract"
val kind = ContractKind.InvariantEntry
# When "checking if invariant"
val is_inv = kind.is_invariant()
# Then "it should return true"
expect(is_inv).to_equal(true)
```

</details>

#### Check if Precondition is checked at entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Precondition contract"
val kind = ContractKind.Precondition
# When "checking if checked at entry"
val at_entry = kind.checked_at_entry()
# Then "it should return true"
expect(at_entry).to_equal(true)
```

</details>

#### Check if Postcondition is checked at exit

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Postcondition contract"
val kind = ContractKind.Postcondition
# When "checking if checked at exit"
val at_exit = kind.checked_at_exit()
# Then "it should return true"
expect(at_exit).to_equal(true)
```

</details>

#### Get name of Saturate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Saturate behavior"
val behavior = UnitOverflowBehavior.Saturate
# When "getting the name"
val name = behavior.name()
# Then "it should return 'saturate'"
expect(name).to_equal("saturate")
```

</details>

#### Check if Default is default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Default behavior"
val behavior = UnitOverflowBehavior.Default
# When "checking if default"
val is_def = behavior.is_default()
# Then "it should return true"
expect(is_def).to_equal(true)
```

</details>

#### Check if Checked is checked

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Checked behavior"
val behavior = UnitOverflowBehavior.Checked
# When "checking if checked"
val is_checked = behavior.is_checked()
# Then "it should return true"
expect(is_checked).to_equal(true)
```

</details>

#### Get name of WorkGroup

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a WorkGroup scope"
val scope = GpuMemoryScope.WorkGroup
# When "getting the name"
val name = scope.name()
# Then "it should return 'workgroup'"
expect(name).to_equal("workgroup")
```

</details>

#### Check if All includes workgroup

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an All scope"
val scope = GpuMemoryScope.All
# When "checking if includes workgroup"
val includes = scope.includes_workgroup()
# Then "it should return true"
expect(includes).to_equal(true)
```

</details>

#### Check if Device includes device

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Device scope"
val scope = GpuMemoryScope.Device
# When "checking if includes device"
val includes = scope.includes_device()
# Then "it should return true"
expect(includes).to_equal(true)
```

</details>

#### Get name of Add

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an Add atomic op"
val op = GpuAtomicOp.Add
# When "getting the name"
val name = op.name()
# Then "it should return 'add'"
expect(name).to_equal("add")
```

</details>

#### Check if Add is arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an Add atomic op"
val op = GpuAtomicOp.Add
# When "checking if arithmetic"
val is_arith = op.is_arithmetic()
# Then "it should return true"
expect(is_arith).to_equal(true)
```

</details>

#### Check if Min is comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Min atomic op"
val op = GpuAtomicOp.Min
# When "checking if comparison"
val is_cmp = op.is_comparison()
# Then "it should return true"
expect(is_cmp).to_equal(true)
```

</details>

#### Check if And is bitwise

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an And atomic op"
val op = GpuAtomicOp.And
# When "checking if bitwise"
val is_bitwise = op.is_bitwise()
# Then "it should return true"
expect(is_bitwise).to_equal(true)
```

</details>

#### Get name of ByValue

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a ByValue capture mode"
val mode = CaptureMode.ByValue
# When "getting the name"
val name = mode.name()
# Then "it should return 'by_value'"
expect(name).to_equal("by_value")
```

</details>

#### Check if ByValue is by value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a ByValue capture mode"
val mode = CaptureMode.ByValue
# When "checking if by value"
val is_val = mode.is_by_value()
# Then "it should return true"
expect(is_val).to_equal(true)
```

</details>

#### Check if ByRef is reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a ByRef capture mode"
val mode = CaptureMode.ByRef
# When "checking if reference"
val is_ref = mode.is_reference()
# Then "it should return true"
expect(is_ref).to_equal(true)
```

</details>

#### Check if ByMutRef is mutable

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a ByMutRef capture mode"
val mode = CaptureMode.ByMutRef
# When "checking if mutable"
val is_mut = mode.is_mutable()
# Then "it should return true"
expect(is_mut).to_equal(true)
```

</details>

#### Get type name of Int

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an Int literal"
val lit = MirLiteral.Int(42)
# When "getting type name"
val type_name = lit.type_name()
# Then "it should return 'int'"
expect(type_name).to_equal("int")
```

</details>

#### Check if Int is number

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an Int literal"
val lit = MirLiteral.Int(42)
# When "checking if number"
val is_num = lit.is_number()
# Then "it should return true"
expect(is_num).to_equal(true)
```

</details>

#### Check if Nil is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Nil literal"
val lit = MirLiteral.Nil
# When "checking if nil"
val is_nil = lit.is_nil()
# Then "it should return true"
expect(is_nil).to_equal(true)
```

</details>

#### Convert true Bool to bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Bool(true) literal"
val lit = MirLiteral.Bool(true)
# When "converting to bool"
val b = lit.to_bool()
# Then "it should return true"
expect(b).to_equal(true)
```

</details>

#### Convert Nil to bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Nil literal"
val lit = MirLiteral.Nil
# When "converting to bool"
val b = lit.to_bool()
# Then "it should return false"
expect(b).to_equal(false)
```

</details>

#### Convert Int(0) to bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an Int(0) literal"
val lit = MirLiteral.Int(0)
# When "converting to bool"
val b = lit.to_bool()
# Then "it should return false"
expect(b).to_equal(false)
```

</details>

#### Convert Int(42) to bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an Int(42) literal"
val lit = MirLiteral.Int(42)
# When "converting to bool"
val b = lit.to_bool()
# Then "it should return true"
expect(b).to_equal(true)
```

</details>

#### Convert TupleIndex to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a TupleIndex(2)"
val step = BindingStep.TupleIndex(2)
# When "converting to string"
val s = step.to_string()
# Then "it should return '.2'"
expect(s).to_equal(".2")
```

</details>

#### Convert FieldName to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a FieldName('x')"
val step = BindingStep.FieldName("x")
# When "converting to string"
val s = step.to_string()
# Then "it should return '.x'"
expect(s).to_equal(".x")
```

</details>

#### Check if TupleIndex is tuple index

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a TupleIndex"
val step = BindingStep.TupleIndex(0)
# When "checking if tuple index"
val is_tuple = step.is_tuple_index()
# Then "it should return true"
expect(is_tuple).to_equal(true)
```

</details>

#### Check if FieldName is field

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a FieldName"
val step = BindingStep.FieldName("field")
# When "checking if field"
val is_field = step.is_field()
# Then "it should return true"
expect(is_field).to_equal(true)
```

</details>

#### Create new binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a binding name 'x'"
val name = "x"
# When "creating new binding"
val binding = PatternBinding.new(name)
# Then "it should have empty path"
expect(binding.path.length()).to_equal(0)
# And "name should be 'x'"
expect(binding.name).to_equal("x")
```

</details>

#### Add step to binding

- var binding = PatternBinding new
- binding add step
   - Expected: binding.path.length() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a binding"
var binding = PatternBinding.new("x")
# When "adding a field step"
binding.add_step(BindingStep.FieldName("y"))
# Then "path should have 1 step"
expect(binding.path.length()).to_equal(1)
```

</details>

#### Get path string

- var binding = PatternBinding new
- binding add step
- binding add step
   - Expected: path equals `point.x.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a binding with steps"
var binding = PatternBinding.new("point")
binding.add_step(BindingStep.FieldName("x"))
binding.add_step(BindingStep.TupleIndex(0))
# When "getting path string"
val path = binding.path_string()
# Then "it should be 'point.x.0'"
expect(path).to_equal("point.x.0")
```

</details>

#### Get path depth

- var binding = PatternBinding new
- binding add step
- binding add step
- binding add step
   - Expected: depth equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a binding with 3 steps"
var binding = PatternBinding.new("data")
binding.add_step(BindingStep.FieldName("nested"))
binding.add_step(BindingStep.FieldName("value"))
binding.add_step(BindingStep.TupleIndex(1))
# When "getting depth"
val depth = binding.depth()
# Then "it should be 3"
expect(depth).to_equal(3)
```

</details>

#### Check if Literal is literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "a Literal part"
val part = FStringPart.Literal("hello")
# When "checking if literal"
val is_lit = part.is_literal()
# Then "it should return true"
expect(is_lit).to_equal(true)
```

</details>

#### Check if Expr is expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an Expr part"
val part = FStringPart.Expr(5)
# When "checking if expression"
val is_expr = part.is_expr()
# Then "it should return true"
expect(is_expr).to_equal(true)
```

</details>

#### Calculate total literal length

- FStringPart Literal
- FStringPart Expr
- FStringPart Literal
- FStringPart Expr
- FStringPart Literal
   - Expected: length equals `26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an f-string with mixed parts"
val parts = [
    FStringPart.Literal("Hello "),
    FStringPart.Expr(0),
    FStringPart.Literal(", you are "),
    FStringPart.Expr(1),
    FStringPart.Literal(" years old")
]
# When "calculating total literal length"
val length = FStringPart.total_literal_length(parts)
# Then "it should be 27 (6 + 11 + 10)"
expect(length).to_equal(26)
```

</details>

#### Count expressions in parts

- FStringPart Literal
- FStringPart Expr
- FStringPart Literal
- FStringPart Expr
- FStringPart Literal
- FStringPart Expr
   - Expected: count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "an f-string with mixed parts"
val parts = [
    FStringPart.Literal("Result: "),
    FStringPart.Expr(0),
    FStringPart.Literal(" + "),
    FStringPart.Expr(1),
    FStringPart.Literal(" = "),
    FStringPart.Expr(2)
]
# When "counting expressions"
val count = FStringPart.count_expressions(parts)
# Then "it should be 3"
expect(count).to_equal(3)
```

</details>

#### Total literal length with no literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "only expression parts"
val parts = [FStringPart.Expr(0), FStringPart.Expr(1)]
# When "calculating literal length"
val length = FStringPart.total_literal_length(parts)
# Then "it should be 0"
expect(length).to_equal(0)
```

</details>

#### Count expressions with no expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Given "only literal parts"
val parts = [FStringPart.Literal("hello"), FStringPart.Literal(" world")]
# When "counting expressions"
val count = FStringPart.count_expressions(parts)
# Then "it should be 0"
expect(count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/mir_types_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
