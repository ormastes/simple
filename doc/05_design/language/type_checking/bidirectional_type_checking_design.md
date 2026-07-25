# Bidirectional Type Checking Design

**Date:** 2026-02-03
**Status:** Design Phase
**Implementation Target:** `src/compiler/type_infer.spl`

---

## Overview

**Current:** Forward-only inference (synthesize mode)
```simple
me infer_expr(expr: HirExpr) -> Result<HirType, TypeInferError>
```

**Goal:** Bidirectional inference (synthesize + check modes)
```simple
me infer_expr(expr: HirExpr, expected: HirType?) -> Result<HirType, TypeInferError>
```

---

## Core Concepts

### 1. Two Modes of Type Checking

**Synthesize Mode** (`expected = None`):
- Infer type from expression structure
- Current behavior (what Simple already does)
- Used when context provides no hint

**Check Mode** (`expected = Some(ty)`):
- Validate expression matches expected type
- Use expected type to resolve ambiguities
- Flow context backward through AST

### 2. When to Use Each Mode

| Expression | Mode | Reason |
|------------|------|--------|
| `42` | Check if expected exists, else Synthesize | Can be i32, i64, u32, etc. depending on context |
| `x + y` | Synthesize operands, Check result | Infer operand types, validate result |
| `f(arg)` | Synthesize `f`, Check `arg` against param type | Expected type from function signature |
| `if cond then a else b` | Check branches against expected | Both branches must match expected |
| `[1, 2, 3]` | Check elements if expected is `[T]` | Array type from context |

---

## Type Definitions

### Add to `type_infer_types.spl`:

```simple
# Inference direction for bidirectional checking
enum InferMode:
    Synthesize    # Infer type from expression
    Check(HirType)  # Check expression matches expected type

# Extended context for bidirectional checking
struct BiContext:
    """Bidirectional type checking context.

    Tracks expected type during inference for better type resolution.
    """
    expected: HirType?   # Expected type from parent context
    mode: InferMode      # Current inference mode
```

---

## Modified Signature

### Before (Unidirectional):
```simple
me infer_expr(expr: HirExpr) -> Result<HirType, TypeInferError>:
    """Infer the type of an expression using Algorithm W."""
    match expr.kind:
        case IntLit(_):
            Ok(HirType(kind: Int(64, true)))  # Always i64
```

### After (Bidirectional):
```simple
me infer_expr(expr: HirExpr, expected: HirType?) -> Result<HirType, TypeInferError>:
    """Infer or check the type of an expression.

    If expected is Some(ty), validates expr has type ty (check mode).
    If expected is None, infers type from expr (synthesize mode).
    """
    match (expr.kind, expected):
        case (IntLit(_), Some(ty)):
            # Check mode: use expected type
            match ty.kind:
                case Int(bits, signed):
                    Ok(ty)  # Accept if target is integer type
                case _:
                    Err(TypeInferError.Mismatch(ty, infer_int_type(expr), expr.span))

        case (IntLit(_), None):
            # Synthesize mode: default to i64
            Ok(HirType(kind: Int(64, true)))
```

---

## Propagation Rules

### Rule 1: Function Calls

**Context:** `f(arg1, arg2)` where `f: fn(T1, T2) -> R`

**Propagation:**
1. Synthesize type of `f` → get function type
2. Extract parameter types `[T1, T2]`
3. **Check** each argument against parameter type:
   - `infer_expr(arg1, Some(T1))`
   - `infer_expr(arg2, Some(T2))`
4. Return `R`

**Implementation:**
```simple
case Call(callee, args, _):
    match self.infer_expr(callee, None):  # Synthesize callee type
        case Ok(callee_ty):
            val resolved = self.resolve(callee_ty)
            match resolved.kind:
                case Function(param_types, ret, _):
                    # Check arguments against parameter types
                    for i in 0..args.len():
                        val arg = args[i].value
                        val param_ty = param_types[i]
                        match self.infer_expr(arg, Some(param_ty)):  # Check mode
                            case Err(e): return Err(e)
                            case _: pass
                    Ok(ret)
                case _:
                    Err(TypeInferError.Other("callee is not a function", span))
        case Err(e): Err(e)
```

### Rule 2: If Expressions

**Context:** `if cond then a else b` with expected type `T`

**Propagation:**
1. **Check** condition is bool: `infer_expr(cond, Some(Bool))`
2. **Check** both branches against expected:
   - `infer_expr(a, expected)`
   - `infer_expr(b, expected)`
3. Return expected type (or unify if no expected)

**Implementation:**
```simple
case If(cond, then_block, else_block):
    # Condition must be bool
    match self.infer_expr(cond, Some(HirType(kind: Bool, span: span))):
        case Err(e): return Err(e)
        case _: pass

    # Check branches against expected type
    match expected:
        case Some(exp_ty):
            # Check mode: both branches must match expected
            match self.infer_expr(then_block, Some(exp_ty)):
                case Err(e): return Err(e)
                case _: pass
            if else_block.?:
                match self.infer_expr(else_block.unwrap(), Some(exp_ty)):
                    case Err(e): return Err(e)
                    case _: pass
            Ok(exp_ty)

        case None:
            # Synthesize mode: infer then branch, check else matches
            match self.infer_expr(then_block, None):
                case Ok(then_ty):
                    if else_block.?:
                        match self.infer_expr(else_block.unwrap(), Some(then_ty)):
                            case Err(e): return Err(e)
                            case _: pass
                    Ok(then_ty)
                case Err(e): Err(e)
```

### Rule 3: Literals with Context

**Context:** Numeric literals with expected type

**Propagation:**
- If expected type is numeric, use it
- Otherwise, use default (i64 for int, f64 for float)

**Implementation:**
```simple
case IntLit(value, suffix):
    match expected:
        case Some(ty):
            # Check if expected type is compatible integer type
            match ty.kind:
                case Int(bits, signed):
                    # Validate literal fits in target type
                    if fits_in_int(value, bits, signed):
                        Ok(ty)
                    else:
                        Err(TypeInferError.Other("literal out of range", span))
                case _:
                    # Expected non-integer, try to synthesize and unify
                    val synth_ty = synthesize_int_type(suffix)
                    self.unify(synth_ty, ty)?
                    Ok(ty)

        case None:
            # Synthesize: use suffix or default to i64
            Ok(synthesize_int_type(suffix))
```

### Rule 4: Array Literals

**Context:** `[e1, e2, e3]` with expected type `[T]`

**Propagation:**
1. If expected is `Array(T, _)`, **check** all elements against `T`
2. Otherwise, **synthesize** from first element, check rest match

**Implementation:**
```simple
case ArrayLit(elements, _):
    match expected:
        case Some(ty):
            # Check mode: validate all elements match expected element type
            match ty.kind:
                case Array(elem_ty, _):
                    for e in elements:
                        match self.infer_expr(e, Some(elem_ty)):
                            case Err(err): return Err(err)
                            case _: pass
                    Ok(ty)
                case _:
                    # Expected non-array type, error
                    Err(TypeInferError.Mismatch(ty, synthesized_array_ty, span))

        case None:
            # Synthesize mode: infer from first element
            if elements.is_empty():
                # Empty array needs type annotation or expected type
                Err(TypeInferError.Other("cannot infer type of empty array", span))
            else:
                match self.infer_expr(elements[0], None):
                    case Ok(elem_ty):
                        # Check remaining elements match
                        for i in 1..elements.len():
                            match self.infer_expr(elements[i], Some(elem_ty)):
                                case Err(e): return Err(e)
                                case _: pass
                        Ok(HirType(kind: Array(elem_ty, None), span: span))
                    case Err(e): Err(e)
```

### Rule 5: Binary Operators

**Context:** `a + b` with expected type `T`

**Propagation:**
1. **Synthesize** left operand type
2. **Check** right operand matches left type
3. Compute result type from operator
4. If expected exists, **unify** with expected

**Implementation:**
```simple
case Binary(op, left, right):
    # Synthesize left operand
    match self.infer_expr(left, None):
        case Ok(left_ty):
            # Check right operand matches left
            match self.infer_expr(right, Some(left_ty)):
                case Ok(right_ty):
                    # Compute result type
                    val result_ty = self.infer_binary_op(op, left_ty, right_ty, span)?

                    # If expected exists, unify
                    match expected:
                        case Some(exp_ty):
                            self.unify(result_ty, exp_ty)?
                            Ok(exp_ty)
                        case None:
                            Ok(result_ty)
                case Err(e): Err(e)
        case Err(e): Err(e)
```

### Rule 6: Lambda Expressions

**Context:** `\x: body` with expected type `fn(T1) -> T2`

**Propagation:**
1. If expected is function type, extract parameter types
2. Bind parameters with extracted types
3. **Check** body against expected return type

**Implementation:**
```simple
case Closure(params, body, _):
    match expected:
        case Some(ty):
            # Check mode: use expected function type
            match ty.kind:
                case Function(param_types, ret_ty, _):
                    if params.len() != param_types.len():
                        return Err(TypeInferError.Other("parameter count mismatch", span))

                    self.enter_level()
                    # Bind parameters with expected types
                    for i in 0..params.len():
                        self.bind_mono(params[i].name, param_types[i])

                    # Check body against expected return type
                    match self.infer_expr(body, Some(ret_ty)):
                        case Ok(_):
                            self.exit_level()
                            Ok(ty)
                        case Err(e):
                            self.exit_level()
                            Err(e)
                case _:
                    # Expected non-function type, error
                    Err(TypeInferError.Mismatch(ty, lambda_ty, span))

        case None:
            # Synthesize mode: infer parameter and return types
            self.enter_level()
            var param_types: [HirType] = []
            for p in params:
                val param_ty = if p.type_.kind != HirTypeKind.Infer(0, 0):
                    p.type_
                else:
                    self.fresh_var(p.span)
                param_types = param_types.push(param_ty)
                self.bind_mono(p.name, param_ty)

            match self.infer_expr(body, None):
                case Ok(body_ty):
                    self.exit_level()
                    Ok(HirType(kind: Function(param_types, body_ty, []), span: span))
                case Err(e):
                    self.exit_level()
                    Err(e)
```

---

## Implementation Plan

### Step 1: Add Type Definitions (1h)

**File:** `src/compiler/type_infer_types.spl`

Add:
```simple
enum InferMode:
    Synthesize
    Check(HirType)
```

### Step 2: Update Function Signature (1h)

**File:** `src/compiler/type_infer.spl`

Change:
```simple
me infer_expr(expr: HirExpr) -> Result<HirType, TypeInferError>
```

To:
```simple
me infer_expr(expr: HirExpr, expected: HirType?) -> Result<HirType, TypeInferError>
```

Update all call sites to pass `None` initially (preserves current behavior).

### Step 3: Implement Check Mode for Literals (2h)

**Target:** IntLit, FloatLit cases

Implement expected type handling for numeric literals:
- Use expected type if compatible
- Validate range fits
- Fall back to default if no expected type

### Step 4: Implement Check Mode for Function Calls (2h)

**Target:** Call case

Flow parameter types to arguments:
- Extract function signature
- Check arguments against parameter types
- Propagate expected types down

### Step 5: Implement Check Mode for If Expressions (2h)

**Target:** If case

Flow expected type to branches:
- Check condition is bool
- Check both branches match expected
- Unify branch types if no expected

### Step 6: Implement Check Mode for Arrays (1h)

**Target:** ArrayLit case

Flow element type to array elements:
- Extract element type from expected
- Check all elements match
- Handle empty arrays with context

### Step 7: Implement Check Mode for Lambdas (2h)

**Target:** Closure case

Flow function signature to lambda:
- Extract parameter/return types
- Bind parameters with types
- Check body against return type

### Step 8: Testing (3h)

Create comprehensive test suite:
- Literal type inference from context
- Function argument checking
- If expression branches
- Array homogeneity
- Lambda parameter inference

---

## Benefits

### 1. Better Type Inference

**Before:**
```simple
val x: i32 = 42  # Need annotation
```

**After:**
```simple
val x: i32 = 42  # 42 inferred as i32 from context
```

### 2. Overload Resolution

**Before:**
```simple
# Can't resolve which overload
print(42)  # Is this print<Int> or print<i32>?
```

**After:**
```simple
# Expected type disambiguates
fn process(x: i32): print(x)  # 42 is i32 because print expects i32
```

### 3. Better Error Messages

**Before:**
```simple
val x: bool = 42
# Error: type mismatch (vague)
```

**After:**
```simple
val x: bool = 42
# Error: expected bool, found i64 at literal '42'
# Help: literal '42' inferred as i64, but bool was expected
```

### 4. Lambda Type Inference

**Before:**
```simple
val f: fn(i32) -> i32 = \x: x * 2  # Need annotation on lambda
```

**After:**
```simple
val f: fn(i32) -> i32 = \x: x * 2  # x inferred as i32 from expected type
```

---

## Compatibility

### Backward Compatibility

All existing code continues to work:
- `infer_expr(expr, None)` behaves like current `infer_expr(expr)`
- No breaking changes to public API
- Tests pass unchanged

### Performance

Minimal overhead:
- One optional parameter (cheap)
- Check mode often faster (fewer fresh variables)
- Same complexity: O(expression size)

---

## Testing Strategy

### Unit Tests

```simple
test "literal type from context":
    var ctx = HmInferContext.new()
    val expr = HirExpr(kind: IntLit(42, None), span: dummy_span)
    val expected = HirType(kind: Int(32, true), span: dummy_span)

    val result = ctx.infer_expr(expr, Some(expected))
    assert result.ok.? and result.unwrap().kind == Int(32, true)

test "function argument checking":
    var ctx = HmInferContext.new()
    # fn add(x: i32, y: i32) -> i32
    val fn_ty = HirType(kind: Function([Int32, Int32], Int32, []), span: dummy_span)
    ctx.bind_mono("add", fn_ty)

    # add(42, 100) - arguments should be checked as i32
    val call = HirExpr(kind: Call(var("add"), [lit(42), lit(100)], []), span: dummy_span)
    val result = ctx.infer_expr(call, None)

    assert result.ok.?

test "if expression branch checking":
    var ctx = HmInferContext.new()
    val expected = HirType(kind: Int(64, true), span: dummy_span)
    val if_expr = HirExpr(
        kind: If(
            bool_lit(true),
            int_lit(42),
            Some(int_lit(100))
        ),
        span: dummy_span
    )

    val result = ctx.infer_expr(if_expr, Some(expected))
    assert result.ok.? and result.unwrap().kind == Int(64, true)
```

### Integration Tests

Test with real Simple code:
```simple
# Should infer correctly
val nums: [i32] = [1, 2, 3, 4, 5]  # Literals inferred as i32

fn double(x: i32) -> i32: x * 2
val f = double  # f: fn(i32) -> i32

val result = [1, 2, 3].map(double)  # Arguments checked against i32
```

---

## Success Criteria

- ✅ All existing tests pass (backward compatible)
- ✅ 20+ new tests for bidirectional checking
- ✅ Numeric literals use context types
- ✅ Function arguments checked against parameters
- ✅ Lambda parameters inferred from expected type
- ✅ Better error messages with expected vs found
- ✅ No performance regression (< 10% overhead)

---

## Timeline

| Step | Task | Time | Total |
|------|------|------|-------|
| 1 | Design (this document) | 2h | 2h |
| 2 | Type definitions | 1h | 3h |
| 3 | Update signatures | 1h | 4h |
| 4 | Literals | 2h | 6h |
| 5 | Function calls | 2h | 8h |
| 6 | If expressions | 2h | 10h |
| 7 | Arrays | 1h | 11h |
| 8 | Lambdas | 2h | 13h |
| 9 | Testing | 3h | 16h |

**Total: 16 hours** (design + implementation + testing)

---

**Status:** Ready for Implementation
**Next:** Step 2 - Add type definitions
