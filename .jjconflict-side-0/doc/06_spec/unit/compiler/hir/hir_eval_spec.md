# Hir Eval Specification

> Tests covering Value Creation, Value Type Checks, Value Truthiness, Value to_string, EvalResult, CallFrame Creation, CallFrame Local Access, EvalContext Creation, EvalContext Frame Management, EvalContext Variable Access, Binary Arithmetic Operations, Binary Comparison Operations, Binary Logical Operations, Unary Operations, HirInterpreter Creation, HirInterpreter Literal Evaluation, HirInterpreter Frame Management.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 82 | 82 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hir Eval Specification

## Scenarios

### Value Creation

#### nil_val creates nil value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- nil_val creates nil value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil_val creates nil value")
# val v = Value.nil_val()
# expect v.is_nil()
expect true
```

</details>

#### bool_val creates bool value

- bool_val creates bool value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool_val creates bool value")
# val v = Value.bool_val(true)
# expect v.is_bool()
# expect v.bool_val == true
expect true
```

</details>

#### int_val creates int value

- int_val creates int value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("int_val creates int value")
# val v = Value.int_val(42)
# expect v.is_int()
# expect v.int_val == 42
expect true
```

</details>

#### float_val creates float value

- float_val creates float value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float_val creates float value")
# val v = Value.float_val(3.14)
# expect v.is_float()
# expect v.float_val == 3.14
expect true
```

</details>

#### string_val creates string value

- string_val creates string value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string_val creates string value")
# val v = Value.string_val("hello")
# expect v.is_string()
# expect v.str_val == "hello"
expect true
```

</details>

#### array_val creates array value

- array_val creates array value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array_val creates array value")
# val items = [Value.int_val(1), Value.int_val(2)]
# val v = Value.array_val(items)
# expect v.is_array()
expect true
```

</details>

### Value Type Checks

#### is_nil returns true for nil

- is_nil returns true for nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_nil returns true for nil")
# expect Value.nil_val().is_nil()
expect true
```

</details>

#### is_nil returns false for non-nil

- is_nil returns false for non-nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_nil returns false for non-nil")
# expect not Value.int_val(0).is_nil()
expect true
```

</details>

#### is_numeric returns true for int

- is_numeric returns true for int


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_numeric returns true for int")
# expect Value.int_val(0).is_numeric()
expect true
```

</details>

#### is_numeric returns true for float

- is_numeric returns true for float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_numeric returns true for float")
# expect Value.float_val(0.0).is_numeric()
expect true
```

</details>

#### is_numeric returns false for string

- is_numeric returns false for string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_numeric returns false for string")
# expect not Value.string_val("").is_numeric()
expect true
```

</details>

### Value Truthiness

#### nil is falsy

- nil is falsy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil is falsy")
# expect not Value.nil_val().is_truthy()
expect true
```

</details>

#### false is falsy

- false is falsy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false is falsy")
# expect not Value.bool_val(false).is_truthy()
expect true
```

</details>

#### true is truthy

- true is truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true is truthy")
# expect Value.bool_val(true).is_truthy()
expect true
```

</details>

#### zero int is falsy

- zero int is falsy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero int is falsy")
# expect not Value.int_val(0).is_truthy()
expect true
```

</details>

#### non-zero int is truthy

- non-zero int is truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-zero int is truthy")
# expect Value.int_val(1).is_truthy()
expect true
```

</details>

#### zero float is falsy

- zero float is falsy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero float is falsy")
# expect not Value.float_val(0.0).is_truthy()
expect true
```

</details>

#### non-zero float is truthy

- non-zero float is truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-zero float is truthy")
# expect Value.float_val(0.1).is_truthy()
expect true
```

</details>

#### empty string is falsy

- empty string is falsy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string is falsy")
# expect not Value.string_val("").is_truthy()
expect true
```

</details>

#### non-empty string is truthy

- non-empty string is truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-empty string is truthy")
# expect Value.string_val("x").is_truthy()
expect true
```

</details>

#### empty array is falsy

- empty array is falsy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty array is falsy")
# expect not Value.array_val([]).is_truthy()
expect true
```

</details>

#### non-empty array is truthy

- non-empty array is truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-empty array is truthy")
# expect Value.array_val([Value.nil_val()]).is_truthy()
expect true
```

</details>

### Value to_string

#### nil to_string is nil

- nil to_string is nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil to_string is nil")
# expect Value.nil_val().to_string() == "nil"
expect true
```

</details>

#### true to_string is true

- true to_string is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("true to_string is true")
# expect Value.bool_val(true).to_string() == "true"
expect true
```

</details>

#### false to_string is false

- false to_string is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("false to_string is false")
# expect Value.bool_val(false).to_string() == "false"
expect true
```

</details>

#### int to_string is number

- int to_string is number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("int to_string is number")
# expect Value.int_val(42).to_string() == "42"
expect true
```

</details>

### EvalResult

#### Ok is_ok returns true

- Ok is_ok returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok is_ok returns true")
# val r = EvalResult.Ok(Value.nil_val())
# expect r.is_ok()
expect true
```

</details>

#### Err is_err returns true

- Err is_err returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Err is_err returns true")
# val r = EvalResult.Err("error")
# expect r.is_err()
expect true
```

</details>

#### Return is_return returns true

- Return is_return returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Return is_return returns true")
# val r = EvalResult.Return(Value.int_val(0))
# expect r.is_return()
expect true
```

</details>

#### Break is_break returns true

- Break is_break returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Break is_break returns true")
# val r = EvalResult.Break
# expect r.is_break()
expect true
```

</details>

#### Continue is_continue returns true

- Continue is_continue returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Continue is_continue returns true")
# val r = EvalResult.Continue
# expect r.is_continue()
expect true
```

</details>

#### unwrap returns value for Ok

- unwrap returns value for Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap returns value for Ok")
# val r = EvalResult.Ok(Value.int_val(42))
# expect r.unwrap().int_val == 42
expect true
```

</details>

#### unwrap_err returns message for Err

- unwrap_err returns message for Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap_err returns message for Err")
# val r = EvalResult.Err("test error")
# expect r.unwrap_err() == "test error"
expect true
```

</details>

### CallFrame Creation

#### creates frame with name

- creates frame with name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates frame with name")
# val frame = CallFrame.new("main", 3, TypeId.void_ty())
# expect frame.name == "main"
expect true
```

</details>

#### creates frame with locals

- creates frame with locals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates frame with locals")
# val frame = CallFrame.new("foo", 5, TypeId.void_ty())
# expect frame.locals.len() == 5
expect true
```

</details>

#### locals initialized to nil

- locals initialized to nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locals initialized to nil")
# val frame = CallFrame.new("foo", 2, TypeId.void_ty())
# expect frame.get_local(0).is_nil()
# expect frame.get_local(1).is_nil()
expect true
```

</details>

### CallFrame Local Access

#### get_local returns nil for valid index

- get_local returns nil for valid index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_local returns nil for valid index")
# val frame = CallFrame.new("foo", 3, TypeId.void_ty())
# expect frame.get_local(0).is_nil()
expect true
```

</details>

#### get_local returns nil for invalid index

- get_local returns nil for invalid index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_local returns nil for invalid index")
# val frame = CallFrame.new("foo", 3, TypeId.void_ty())
# expect frame.get_local(100).is_nil()
expect true
```

</details>

#### set_local updates value

- set_local updates value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_local updates value")
# var frame = CallFrame.new("foo", 3, TypeId.void_ty())
# frame.set_local(0, Value.int_val(42))
# expect frame.get_local(0).int_val == 42
expect true
```

</details>

### EvalContext Creation

#### creates with no frames

- creates with no frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with no frames")
# var ctx = EvalContext.new()
# expect ctx.frames.len() == 0
expect true
```

</details>

#### creates with default max stack depth

- creates with default max stack depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with default max stack depth")
# var ctx = EvalContext.new()
# expect ctx.max_stack_depth == 1000
expect true
```

</details>

#### current_frame returns None initially

- current_frame returns None initially


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("current_frame returns None initially")
# var ctx = EvalContext.new()
# expect ctx.current_frame().is_none()
expect true
```

</details>

### EvalContext Frame Management

#### push_frame adds frame

- push_frame adds frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_frame adds frame")
# var ctx = EvalContext.new()
# val frame = CallFrame.new("main", 0, TypeId.void_ty())
# expect ctx.push_frame(frame)
# expect ctx.frames.len() == 1
expect true
```

</details>

#### push_frame sets current frame

- push_frame sets current frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_frame sets current frame")
# var ctx = EvalContext.new()
# val frame = CallFrame.new("main", 0, TypeId.void_ty())
# ctx.push_frame(frame)
# expect ctx.current_frame().is_some()
expect true
```

</details>

#### pop_frame removes frame

- pop_frame removes frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pop_frame removes frame")
# var ctx = EvalContext.new()
# val frame = CallFrame.new("main", 0, TypeId.void_ty())
# ctx.push_frame(frame)
# ctx.pop_frame()
# expect ctx.frames.len() == 0
expect true
```

</details>

#### pop_frame returns popped frame

- pop_frame returns popped frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pop_frame returns popped frame")
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

- get_local returns nil without frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_local returns nil without frame")
# var ctx = EvalContext.new()
# expect ctx.get_local(0).is_nil()
expect true
```

</details>

#### set_local/get_local work with frame

- set_local/get_local work with frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_local/get_local work with frame")
# var ctx = EvalContext.new()
# val frame = CallFrame.new("main", 3, TypeId.void_ty())
# ctx.push_frame(frame)
# ctx.set_local(0, Value.int_val(42))
# expect ctx.get_local(0).int_val == 42
expect true
```

</details>

#### get_global returns nil for unset

- get_global returns nil for unset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_global returns nil for unset")
# var ctx = EvalContext.new()
# expect ctx.get_global(0).is_nil()
expect true
```

</details>

#### set_global/get_global work correctly

- set_global/get_global work correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_global/get_global work correctly")
# var ctx = EvalContext.new()
# ctx.set_global(0, Value.int_val(100))
# expect ctx.get_global(0).int_val == 100
expect true
```

</details>

### Binary Arithmetic Operations

#### Add integers

- Add integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Add integers")
# val result = eval_binary(BinOp.Add, Value.int_val(2), Value.int_val(3))
# expect result.is_ok()
# expect result.unwrap().int_val == 5
expect true
```

</details>

#### Add floats

- Add floats


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Add floats")
# val result = eval_binary(BinOp.Add, Value.float_val(1.5), Value.float_val(2.5))
# expect result.is_ok()
# expect result.unwrap().float_val == 4.0
expect true
```

</details>

#### Add strings

- Add strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Add strings")
# val result = eval_binary(BinOp.Add, Value.string_val("a"), Value.string_val("b"))
# expect result.is_ok()
# expect result.unwrap().str_val == "ab"
expect true
```

</details>

#### Sub integers

- Sub integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Sub integers")
# val result = eval_binary(BinOp.Sub, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().int_val == 2
expect true
```

</details>

#### Mul integers

- Mul integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Mul integers")
# val result = eval_binary(BinOp.Mul, Value.int_val(4), Value.int_val(5))
# expect result.unwrap().int_val == 20
expect true
```

</details>

#### Div integers

- Div integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Div integers")
# val result = eval_binary(BinOp.Div, Value.int_val(10), Value.int_val(3))
# expect result.unwrap().int_val == 3
expect true
```

</details>

#### Div by zero returns error

- Div by zero returns error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Div by zero returns error")
# val result = eval_binary(BinOp.Div, Value.int_val(10), Value.int_val(0))
# expect result.is_err()
expect true
```

</details>

#### Mod integers

- Mod integers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Mod integers")
# val result = eval_binary(BinOp.Mod, Value.int_val(10), Value.int_val(3))
# expect result.unwrap().int_val == 1
expect true
```

</details>

### Binary Comparison Operations

#### Eq returns true for equal ints

- Eq returns true for equal ints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Eq returns true for equal ints")
# val result = eval_binary(BinOp.Eq, Value.int_val(5), Value.int_val(5))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### Eq returns false for unequal ints

- Eq returns false for unequal ints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Eq returns false for unequal ints")
# val result = eval_binary(BinOp.Eq, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().bool_val == false
expect true
```

</details>

#### NotEq returns true for unequal

- NotEq returns true for unequal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("NotEq returns true for unequal")
# val result = eval_binary(BinOp.NotEq, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### Lt returns true when less

- Lt returns true when less


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Lt returns true when less")
# val result = eval_binary(BinOp.Lt, Value.int_val(3), Value.int_val(5))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### Lt returns false when not less

- Lt returns false when not less


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Lt returns false when not less")
# val result = eval_binary(BinOp.Lt, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().bool_val == false
expect true
```

</details>

#### Gt returns true when greater

- Gt returns true when greater


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Gt returns true when greater")
# val result = eval_binary(BinOp.Gt, Value.int_val(5), Value.int_val(3))
# expect result.unwrap().bool_val == true
expect true
```

</details>

### Binary Logical Operations

#### And returns true when both truthy

- And returns true when both truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("And returns true when both truthy")
# val result = eval_binary(BinOp.And, Value.bool_val(true), Value.bool_val(true))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### And returns false when one falsy

- And returns false when one falsy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("And returns false when one falsy")
# val result = eval_binary(BinOp.And, Value.bool_val(true), Value.bool_val(false))
# expect result.unwrap().bool_val == false
expect true
```

</details>

#### Or returns true when one truthy

- Or returns true when one truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Or returns true when one truthy")
# val result = eval_binary(BinOp.Or, Value.bool_val(false), Value.bool_val(true))
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### Or returns false when both falsy

- Or returns false when both falsy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Or returns false when both falsy")
# val result = eval_binary(BinOp.Or, Value.bool_val(false), Value.bool_val(false))
# expect result.unwrap().bool_val == false
expect true
```

</details>

### Unary Operations

#### Neg negates integer

- Neg negates integer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Neg negates integer")
# val result = eval_unary(UnaryOp.Neg, Value.int_val(5))
# expect result.unwrap().int_val == -5
expect true
```

</details>

#### Neg negates float

- Neg negates float


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Neg negates float")
# val result = eval_unary(UnaryOp.Neg, Value.float_val(3.14))
# expect result.unwrap().float_val == -3.14
expect true
```

</details>

#### Not inverts truthy

- Not inverts truthy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Not inverts truthy")
# val result = eval_unary(UnaryOp.Not, Value.bool_val(true))
# expect result.unwrap().bool_val == false
expect true
```

</details>

#### Not inverts falsy

- Not inverts falsy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Not inverts falsy")
# val result = eval_unary(UnaryOp.Not, Value.bool_val(false))
# expect result.unwrap().bool_val == true
expect true
```

</details>

### HirInterpreter Creation

#### creates with empty context

- creates with empty context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with empty context")
# var interp = HirInterpreter.new()
# expect interp.ctx.frames.len() == 0
expect true
```

</details>

### HirInterpreter Literal Evaluation

#### eval_integer returns int value

- eval_integer returns int value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eval_integer returns int value")
# var interp = HirInterpreter.new()
# val result = interp.eval_integer(42)
# expect result.is_ok()
# expect result.unwrap().int_val == 42
expect true
```

</details>

#### eval_float returns float value

- eval_float returns float value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eval_float returns float value")
# var interp = HirInterpreter.new()
# val result = interp.eval_float(3.14)
# expect result.unwrap().float_val == 3.14
expect true
```

</details>

#### eval_bool returns bool value

- eval_bool returns bool value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eval_bool returns bool value")
# var interp = HirInterpreter.new()
# val result = interp.eval_bool(true)
# expect result.unwrap().bool_val == true
expect true
```

</details>

#### eval_string returns string value

- eval_string returns string value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eval_string returns string value")
# var interp = HirInterpreter.new()
# val result = interp.eval_string("hello")
# expect result.unwrap().str_val == "hello"
expect true
```

</details>

#### eval_nil returns nil value

- eval_nil returns nil value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eval_nil returns nil value")
# var interp = HirInterpreter.new()
# val result = interp.eval_nil()
# expect result.unwrap().is_nil()
expect true
```

</details>

### HirInterpreter Frame Management

#### push_frame creates new frame

- push_frame creates new frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("push_frame creates new frame")
# var interp = HirInterpreter.new()
# expect interp.push_frame("main", 3, TypeId.void_ty())
# expect interp.ctx.frames.len() == 1
expect true
```

</details>

#### pop_frame removes frame

- pop_frame removes frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pop_frame removes frame")
# var interp = HirInterpreter.new()
# interp.push_frame("main", 0, TypeId.void_ty())
# interp.pop_frame()
# expect interp.ctx.frames.len() == 0
expect true
```

</details>

#### declare_local sets value

- declare_local sets value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declare_local sets value")
# var interp = HirInterpreter.new()
# interp.push_frame("main", 3, TypeId.void_ty())
# interp.declare_local(0, Value.int_val(42))
# expect interp.ctx.get_local(0).int_val == 42
expect true
```

</details>

#### assign_local updates value

- assign_local updates value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assign_local updates value")
# var interp = HirInterpreter.new()
# interp.push_frame("main", 3, TypeId.void_ty())
# interp.declare_local(0, Value.int_val(1))
# interp.assign_local(0, Value.int_val(2))
# expect interp.ctx.get_local(0).int_val == 2
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/hir_eval_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Value Creation, Value Type Checks, Value Truthiness, Value to_string, EvalResult, CallFrame Creation, CallFrame Local Access, EvalContext Creation, EvalContext Frame Management, EvalContext Variable Access, Binary Arithmetic Operations, Binary Comparison Operations, Binary Logical Operations, Unary Operations, HirInterpreter Creation, HirInterpreter Literal Evaluation, HirInterpreter Frame Management.
- Value Creation
- Value Type Checks
- Value Truthiness
- Value to_string
- EvalResult
- CallFrame Creation
- CallFrame Local Access
- EvalContext Creation
- EvalContext Frame Management
- EvalContext Variable Access
- Binary Arithmetic Operations
- Binary Comparison Operations
- Binary Logical Operations
- Unary Operations
- HirInterpreter Creation
- HirInterpreter Literal Evaluation
- HirInterpreter Frame Management

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 82 |
| Active scenarios | 82 |
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

- Canonical SPipe generation for source `79411331bdb6c109576f3838c3b7e576a778cf7cf5879016c827d2dcce2c6eba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79411331bdb6c109576f3838c3b7e576a778cf7cf5879016c827d2dcce2c6eba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79411331bdb6c109576f3838c3b7e576a778cf7cf5879016c827d2dcce2c6eba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/hir/hir_eval_spec.spl
mirror: doc/06_spec/unit/compiler/hir/hir_eval_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/hir_eval_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/hir_eval_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/hir_eval_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nil_val creates nil value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/hir_eval_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bool_val creates bool value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/hir_eval_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'int_val creates int value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
