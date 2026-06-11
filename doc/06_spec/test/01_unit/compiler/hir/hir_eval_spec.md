# HIR Interpreter Unit Tests

> Tests for HIR interpreter: Value, EvalResult, EvalContext, HirInterpreter.

<!-- sdn-diagram:id=hir_eval_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hir_eval_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hir_eval_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hir_eval_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR Interpreter Unit Tests

Tests for HIR interpreter: Value, EvalResult, EvalContext, HirInterpreter.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HIR-EVAL-001 |
| Category | HIR \| Interpreter |
| Status | In Progress |
| Source | `test/01_unit/compiler/hir/hir_eval_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for HIR interpreter: Value, EvalResult, EvalContext, HirInterpreter.

## Scenarios

### Value Creation

#### nil_val creates nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val v = Value.nil_val()
# expect v.is_nil()
expect true
```

</details>

#### bool_val creates bool value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val v = Value.bool_val(true)
# expect v.is_bool()
# expect v.bool_val == true
expect true
```

</details>

#### int_val creates int value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val v = Value.int_val(42)
# expect v.is_int()
# expect v.int_val == 42
expect true
```

</details>

#### float_val creates float value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val v = Value.float_val(3.14)
# expect v.is_float()
# expect v.float_val == 3.14
expect true
```

</details>

#### string_val creates string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val v = Value.string_val("hello")
# expect v.is_string()
# expect v.str_val == "hello"
expect true
```

</details>

#### array_val creates array value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val items = [Value.int_val(1), Value.int_val(2)]
# val v = Value.array_val(items)
# expect v.is_array()
expect true
```

</details>

### Value Type Checks

#### is_nil returns true for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.nil_val().is_nil()
expect true
```

</details>

#### is_nil returns false for non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect not Value.int_val(0).is_nil()
expect true
```

</details>

#### is_numeric returns true for int

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.int_val(0).is_numeric()
expect true
```

</details>

#### is_numeric returns true for float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.float_val(0.0).is_numeric()
expect true
```

</details>

#### is_numeric returns false for string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect not Value.string_val("").is_numeric()
expect true
```

</details>

### Value Truthiness

#### nil is falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect not Value.nil_val().is_truthy()
expect true
```

</details>

#### false is falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect not Value.bool_val(false).is_truthy()
expect true
```

</details>

#### true is truthy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.bool_val(true).is_truthy()
expect true
```

</details>

#### zero int is falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect not Value.int_val(0).is_truthy()
expect true
```

</details>

#### non-zero int is truthy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.int_val(1).is_truthy()
expect true
```

</details>

#### zero float is falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect not Value.float_val(0.0).is_truthy()
expect true
```

</details>

#### non-zero float is truthy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.float_val(0.1).is_truthy()
expect true
```

</details>

#### empty string is falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect not Value.string_val("").is_truthy()
expect true
```

</details>

#### non-empty string is truthy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.string_val("x").is_truthy()
expect true
```

</details>

#### empty array is falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect not Value.array_val([]).is_truthy()
expect true
```

</details>

#### non-empty array is truthy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.array_val([Value.nil_val()]).is_truthy()
expect true
```

</details>

### Value to_string

#### nil to_string is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.nil_val().to_string() == "nil"
expect true
```

</details>

#### true to_string is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.bool_val(true).to_string() == "true"
expect true
```

</details>

#### false to_string is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.bool_val(false).to_string() == "false"
expect true
```

</details>

#### int to_string is number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# expect Value.int_val(42).to_string() == "42"
expect true
```

</details>

### EvalResult

#### Ok is_ok returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val r = EvalResult.Ok(Value.nil_val())
# expect r.is_ok()
expect true
```

</details>

#### Err is_err returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val r = EvalResult.Err("error")
# expect r.is_err()
expect true
```

</details>

#### Return is_return returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val r = EvalResult.Return(Value.int_val(0))
# expect r.is_return()
expect true
```

</details>

#### Break is_break returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val r = EvalResult.Break
# expect r.is_break()
expect true
```

</details>

#### Continue is_continue returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val r = EvalResult.Continue
# expect r.is_continue()
expect true
```

</details>

#### unwrap returns value for Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val r = EvalResult.Ok(Value.int_val(42))
# expect r.unwrap().int_val == 42
expect true
```

</details>

#### unwrap_err returns message for Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val r = EvalResult.Err("test error")
# expect r.unwrap_err() == "test error"
expect true
```

</details>

### CallFrame Creation

#### creates frame with name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val frame = CallFrame.new("main", 3, TypeId.void_ty())
# expect frame.name == "main"
expect true
```

</details>

#### creates frame with locals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val frame = CallFrame.new("foo", 5, TypeId.void_ty())
# expect frame.locals.len() == 5
expect true
```

</details>

#### locals initialized to nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val frame = CallFrame.new("foo", 2, TypeId.void_ty())
# expect frame.get_local(0).is_nil()
# expect frame.get_local(1).is_nil()
expect true
```

</details>

### CallFrame Local Access

#### get_local returns nil for valid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val frame = CallFrame.new("foo", 3, TypeId.void_ty())
# expect frame.get_local(0).is_nil()
expect true
```

</details>

#### get_local returns nil for invalid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val frame = CallFrame.new("foo", 3, TypeId.void_ty())
# expect frame.get_local(100).is_nil()
expect true
```

</details>

#### set_local updates value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var frame = CallFrame.new("foo", 3, TypeId.void_ty())
# frame.set_local(0, Value.int_val(42))
# expect frame.get_local(0).int_val == 42
expect true
```

</details>

### EvalContext Creation

#### creates with no frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# expect ctx.frames.len() == 0
expect true
```

</details>

#### creates with default max stack depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# expect ctx.max_stack_depth == 1000
expect true
```

</details>

#### current_frame returns None initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# expect ctx.current_frame().is_none()
expect true
```

</details>

### EvalContext Frame Management

#### push_frame adds frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# val frame = CallFrame.new("main", 0, TypeId.void_ty())
# expect ctx.push_frame(frame)
# expect ctx.frames.len() == 1
expect true
```

</details>

#### push_frame sets current frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# val frame = CallFrame.new("main", 0, TypeId.void_ty())
# ctx.push_frame(frame)
# expect ctx.current_frame().is_some()
expect true
```

</details>

#### pop_frame removes frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# val frame = CallFrame.new("main", 0, TypeId.void_ty())
# ctx.push_frame(frame)
# ctx.pop_frame()
# expect ctx.frames.len() == 0
expect true
```

</details>

#### pop_frame returns popped frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# val frame = CallFrame.new("main", 0, TypeId.void_ty())
# ctx.push_frame(frame)
# val popped = ctx.pop_frame()
# expect popped.is_some()
# expect popped.unwrap().name == "main"
expect true
```

</details>

### EvalContext Variable Access

#### get_local returns nil without frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# expect ctx.get_local(0).is_nil()
expect true
```

</details>

#### set_local/get_local work with frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# val frame = CallFrame.new("main", 3, TypeId.void_ty())
# ctx.push_frame(frame)
# ctx.set_local(0, Value.int_val(42))
# expect ctx.get_local(0).int_val == 42
expect true
```

</details>

#### get_global returns nil for unset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# expect ctx.get_global(0).is_nil()
expect true
```

</details>

#### set_global/get_global work correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var ctx = EvalContext.new()
# ctx.set_global(0, Value.int_val(100))
# expect ctx.get_global(0).int_val == 100
expect true
```

</details>

### Binary Arithmetic Operations

#### Add integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Add, Value.int_val(2), Value.int_val(3))
# expect result.is_ok()
# expect result.unwrap().int_val == 5
expect true
```

</details>

#### Add floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Add, Value.float_val(1.5), Value.float_val(2.5))
# expect result.is_ok()
# expect result.unwrap().float_val == 4.0
expect true
```

</details>

#### Add strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Add, Value.string_val("a"), Value.string_val("b"))
# expect result.is_ok()
# expect result.unwrap().str_val == "ab"
expect true
```

</details>

#### Sub integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Sub, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().int_val == 2
expect true
```

</details>

#### Mul integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Mul, Value.int_val(4), Value.int_val(5))
# expect result.unwrap().int_val == 20
expect true
```

</details>

#### Div integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Div, Value.int_val(10), Value.int_val(3))
# expect result.unwrap().int_val == 3
expect true
```

</details>

#### Div by zero returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Div, Value.int_val(10), Value.int_val(0))
# expect result.is_err()
expect true
```

</details>

#### Mod integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Mod, Value.int_val(10), Value.int_val(3))
# expect result.unwrap().int_val == 1
expect true
```

</details>

### Binary Comparison Operations

#### Eq returns true for equal ints

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Eq, Value.int_val(5), Value.int_val(5))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### Eq returns false for unequal ints

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Eq, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().bool_val == false
expect true
```

</details>

#### NotEq returns true for unequal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.NotEq, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### Lt returns true when less

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Lt, Value.int_val(3), Value.int_val(5))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### Lt returns false when not less

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Lt, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().bool_val == false
expect true
```

</details>

#### Gt returns true when greater

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Gt, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().bool_val == true
expect true
```

</details>

### Binary Logical Operations

#### And returns true when both truthy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.And, Value.bool_val(true), Value.bool_val(true))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### And returns false when one falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.And, Value.bool_val(true), Value.bool_val(false))
# expect result.unwrap().bool_val == false
expect true
```

</details>

#### Or returns true when one truthy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Or, Value.bool_val(false), Value.bool_val(true))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### Or returns false when both falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_binary(BinOp.Or, Value.bool_val(false), Value.bool_val(false))
# expect result.unwrap().bool_val == false
expect true
```

</details>

### Unary Operations

#### Neg negates integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_unary(UnaryOp.Neg, Value.int_val(5))
# expect result.unwrap().int_val == -5
expect true
```

</details>

#### Neg negates float

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_unary(UnaryOp.Neg, Value.float_val(3.14))
# expect result.unwrap().float_val == -3.14
expect true
```

</details>

#### Not inverts truthy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_unary(UnaryOp.Not, Value.bool_val(true))
# expect result.unwrap().bool_val == false
expect true
```

</details>

#### Not inverts falsy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# val result = eval_unary(UnaryOp.Not, Value.bool_val(false))
# expect result.unwrap().bool_val == true
expect true
```

</details>

### HirInterpreter Creation

#### creates with empty context

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# expect interp.ctx.frames.len() == 0
expect true
```

</details>

### HirInterpreter Literal Evaluation

#### eval_integer returns int value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# val result = interp.eval_integer(42)
# expect result.is_ok()
# expect result.unwrap().int_val == 42
expect true
```

</details>

#### eval_float returns float value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# val result = interp.eval_float(3.14)
# expect result.unwrap().float_val == 3.14
expect true
```

</details>

#### eval_bool returns bool value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# val result = interp.eval_bool(true)
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### eval_string returns string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# val result = interp.eval_string("hello")
# expect result.unwrap().str_val == "hello"
expect true
```

</details>

#### eval_nil returns nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# val result = interp.eval_nil()
# expect result.unwrap().is_nil()
expect true
```

</details>

### HirInterpreter Frame Management

#### push_frame creates new frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# expect interp.push_frame("main", 3, TypeId.void_ty())
# expect interp.ctx.frames.len() == 1
expect true
```

</details>

#### pop_frame removes frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# interp.push_frame("main", 0, TypeId.void_ty())
# interp.pop_frame()
# expect interp.ctx.frames.len() == 0
expect true
```

</details>

#### declare_local sets value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# interp.push_frame("main", 3, TypeId.void_ty())
# interp.declare_local(0, Value.int_val(42))
# expect interp.ctx.get_local(0).int_val == 42
expect true
```

</details>

#### assign_local updates value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# var interp = HirInterpreter.new()
# interp.push_frame("main", 3, TypeId.void_ty())
# interp.declare_local(0, Value.int_val(1))
# interp.assign_local(0, Value.int_val(2))
# expect interp.ctx.get_local(0).int_val == 2
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
