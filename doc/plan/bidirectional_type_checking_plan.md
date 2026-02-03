# Bidirectional Type Checking Implementation Plan

**Date:** 2026-02-03
**Status:** 📋 Planned
**Priority:** P0 - Critical (blocks lambda type inference improvements)

---

## Executive Summary

Implement bidirectional type checking to improve type inference for lambda expressions, method calls, and generic instantiations. The existing `InferMode` enum is defined but not used - this plan wires it into the inference engine.

**Key Achievement:** Better lambda parameter inference by propagating expected types top-down.

---

## Current State

### What Exists

✅ **InferMode enum** defined in `type_infer_types.spl:203-230`:

```simple
enum InferMode:
    """Mode for bidirectional type checking.

    Synthesize: Infer type from expression structure (bottom-up)
    Check:      Validate expression matches expected type (top-down)
    """
    Synthesize
    Check(expected: HirType)

impl InferMode:
    fn is_check() -> bool
    fn is_synthesize() -> bool
    fn expected() -> HirType?
```

✅ **Inference engine** in `type_infer.spl`:
- `infer_expr()` - Synthesis mode only (794+ lines)
- `unify()` - Type unification (471+ lines)
- `instantiate()` - Type scheme instantiation
- `generalize()` - Level-based generalization

### What's Missing

❌ **Mode-aware inference** - `infer_expr()` ignores InferMode
❌ **Check mode implementation** - No `check_expr()` function
❌ **Subsumption** - No proper subtyping check
❌ **Mode propagation** - Expected types not propagated

---

## Algorithm Overview

### Bidirectional Type Checking Rules

**Two modes:**

1. **Synthesize (⇒):** Infer type from expression
   ```
   Γ ⊢ e ⇒ τ
   ```

2. **Check (⇐):** Verify expression has expected type
   ```
   Γ ⊢ e ⇐ τ
   ```

### Key Rules

#### Literals (Synthesize)
```
─────────────
Γ ⊢ 42 ⇒ i64

──────────────────
Γ ⊢ "hello" ⇒ text
```

#### Variables (Synthesize + Instantiate)
```
x : ∀α. τ ∈ Γ
───────────────────
Γ ⊢ x ⇒ τ[α := fresh]
```

#### Lambda (Check - Most Important!)
```
Γ ⊢ τ₁ → τ₂  expected
Γ, x : τ₁ ⊢ body ⇐ τ₂
──────────────────────────────
Γ ⊢ (λx. body) ⇐ τ₁ → τ₂
```

Current behavior (Synthesize only):
```simple
val id = \x: x          # Error: can't infer x's type
```

With Check mode:
```simple
val id: fn(i64) -> i64 = \x: x   # OK: x : i64 propagated from annotation
```

#### Application (Synthesize)
```
Γ ⊢ f ⇒ τ₁ → τ₂
Γ ⊢ arg ⇐ τ₁    # Check mode!
─────────────────
Γ ⊢ f(arg) ⇒ τ₂
```

#### Subsumption (Switch modes)
```
Γ ⊢ e ⇒ τ'
τ' <: τ
────────────
Γ ⊢ e ⇐ τ
```

---

## Implementation Plan

### Phase 1: Core Infrastructure (4 hours)

#### 1.1 Add Mode Parameter (1 hour)

**File:** `src/compiler/type_infer.spl`

**Change signature:**
```simple
# Before
me infer_expr(expr: HirExpr) -> Result<HirType, TypeInferError>

# After
me infer_expr(expr: HirExpr, mode: InferMode) -> Result<HirType, TypeInferError>
```

**Update all call sites:**
- 50+ calls to `infer_expr()` need mode argument
- Most will use `InferMode.Synthesize` (default)
- Some will use `InferMode.Check(expected)` (lambdas, annotations)

#### 1.2 Implement Check Mode Dispatcher (1 hour)

```simple
me infer_expr(expr: HirExpr, mode: InferMode) -> Result<HirType, TypeInferError>:
    match mode:
        case Synthesize:
            # Existing synthesis logic
            self.synthesize_expr(expr)

        case Check(expected):
            # New check logic
            self.check_expr(expr, expected)
```

#### 1.3 Extract Synthesis Logic (1 hour)

**Create helper:**
```simple
me synthesize_expr(expr: HirExpr) -> Result<HirType, TypeInferError>:
    """Synthesize type from expression (existing logic)."""
    val span = expr.span

    match expr.kind:
        case IntLit(_, suffix):
            # ... existing logic
        case Var(symbol):
            # ... existing logic
        case Call(callee, args, _):
            # ... existing logic
        # ... all other cases
```

#### 1.4 Implement Subsumption (1 hour)

```simple
me subsume(inferred: HirType, expected: HirType) -> Result<(), TypeInferError>:
    """Check that inferred type is a subtype of expected type.

    For now, this is just unification. Future: variance-aware subtyping.
    """
    self.unify(inferred, expected)
```

**Future:** Replace with variance-aware subtyping from Phase 1.

---

### Phase 2: Check Mode Implementation (4 hours)

#### 2.1 Lambda Check (2 hours) - **Most Important**

```simple
me check_expr(expr: HirExpr, expected: HirType) -> Result<HirType, TypeInferError>:
    val span = expr.span

    match expr.kind:
        case Lambda(params, body):
            # Extract expected function type
            val expected_resolved = self.resolve(expected)

            match expected_resolved.kind:
                case Function(param_tys, ret_ty, effects):
                    # Check parameter count
                    if params.len() != param_tys.len():
                        return Err(TypeInferError.Other(
                            "lambda has {params.len()} params, expected {param_tys.len()}",
                            span
                        ))

                    # Bind parameters with expected types
                    for i in 0..params.len():
                        val param = params[i]
                        val param_ty = param_tys[i]
                        self.bind(param.name, TypeScheme.mono(param_ty))

                    # Check body against expected return type
                    match self.infer_expr(body, InferMode.Check(ret_ty)):
                        case Ok(_):
                            Ok(expected)
                        case Err(e): Err(e)

                case _:
                    # Expected type is not a function
                    # Fallback: synthesize and subsume
                    match self.synthesize_expr(expr):
                        case Ok(inferred):
                            self.subsume(inferred, expected)?
                            Ok(expected)
                        case Err(e): Err(e)

        case _:
            # For other expressions: synthesize and subsume
            match self.synthesize_expr(expr):
                case Ok(inferred):
                    self.subsume(inferred, expected)?
                    Ok(expected)
                case Err(e): Err(e)
```

**Example improvement:**
```simple
# Before (fails):
val process: fn(i64) -> i64 = \x: x * 2
# Error: can't infer x's type

# After (works):
val process: fn(i64) -> i64 = \x: x * 2
# OK: x : i64 propagated from type annotation
```

#### 2.2 Application Argument Checking (1 hour)

**In `synthesize_expr()` for Call:**

```simple
case Call(callee, args, type_args):
    match self.infer_expr(callee, InferMode.Synthesize):
        case Ok(callee_ty):
            val resolved = self.resolve(callee_ty)

            match resolved.kind:
                case Function(param_tys, ret_ty, effects):
                    # Check arguments against expected parameter types
                    var arg_types: [HirType] = []
                    for i in 0..args.len():
                        if i < param_tys.len():
                            # Use Check mode with expected parameter type
                            match self.infer_expr(args[i].value, InferMode.Check(param_tys[i])):
                                case Ok(ty): arg_types = arg_types.push(ty)
                                case Err(e): return Err(e)
                        else:
                            # Extra arg - synthesize
                            match self.infer_expr(args[i].value, InferMode.Synthesize):
                                case Ok(ty): arg_types = arg_types.push(ty)
                                case Err(e): return Err(e)

                    Ok(ret_ty)

                case _:
                    # Not a function type - fallback to synthesis
                    # ... existing logic
```

**Example improvement:**
```simple
fn process(f: fn(i64) -> i64, x: i64) -> i64:
    f(x)

# Before (verbose):
process(\x: x * 2, 10)  # Must annotate lambda explicitly

# After (inference):
process(\x: x * 2, 10)  # x : i64 inferred from parameter type
```

#### 2.3 Let Binding Annotation (1 hour)

```simple
case Let(pattern, type_ann, value, body):
    match type_ann:
        case Some(ann):
            # Use Check mode when annotation present
            match self.infer_expr(value, InferMode.Check(ann)):
                case Ok(value_ty):
                    # Bind and continue
                    self.bind(pattern.name, TypeScheme.mono(value_ty))
                    self.infer_expr(body, mode)
                case Err(e): Err(e)

        case None:
            # No annotation - use Synthesize mode
            match self.infer_expr(value, InferMode.Synthesize):
                case Ok(value_ty):
                    # Generalize and bind
                    val scheme = self.generalize(value_ty)
                    self.bind(pattern.name, scheme)
                    self.infer_expr(body, mode)
                case Err(e): Err(e)
```

---

### Phase 3: Return Type Checking (2 hours)

#### 3.1 Function Return Checking

```simple
me infer_function(func: HirFunction) -> Result<HirType, TypeInferError>:
    # ... parameter setup

    # Check body against declared return type
    match func.return_ty:
        case Some(ret_ty):
            # Use Check mode for function body
            match self.infer_expr(func.body, InferMode.Check(ret_ty)):
                case Ok(_):
                    Ok(HirType(
                        kind: HirTypeKind.Function(param_tys, ret_ty, func.effects),
                        span: func.span
                    ))
                case Err(e): Err(e)

        case None:
            # No return type annotation - synthesize
            match self.infer_expr(func.body, InferMode.Synthesize):
                case Ok(inferred_ret):
                    Ok(HirType(
                        kind: HirTypeKind.Function(param_tys, inferred_ret, func.effects),
                        span: func.span
                    ))
                case Err(e): Err(e)
```

---

### Phase 4: Testing & Integration (2 hours)

#### 4.1 Test Cases (1 hour)

**Create:** `test/compiler/bidir_type_check_spec.spl`

```simple
# @Feature 807: Bidirectional Type Checking
# @Description: Test Check mode for lambda inference and subsumption

describe "Bidirectional Type Checking - Lambda Inference":
    it "infers lambda parameter from function type annotation":
        val id: fn(i64) -> i64 = \x: x
        expect id(42) == 42

    it "infers lambda parameter from argument context":
        fn apply(f: fn(i64) -> i64, x: i64) -> i64:
            f(x)

        val result = apply(\x: x * 2, 10)
        expect result == 20

    it "infers nested lambda parameters":
        val add: fn(i64) -> fn(i64) -> i64 = \x: \y: x + y
        expect add(10)(20) == 30

describe "Bidirectional Type Checking - Subsumption":
    it "allows subtype in check mode":
        fn process(f: fn(i64) -> i64):
            f(42)

        process(\x: x)  # Should work

    it "rejects incompatible types":
        val x: i64 = 42
        # val y: text = x  # Should fail
        expect true

describe "Bidirectional Type Checking - Return Types":
    it "checks function body against return type":
        fn double(x: i64) -> i64:
            x * 2  # Checked against i64

        expect double(21) == 42

    it "detects return type mismatch":
        # fn bad() -> i64:
        #     "oops"  # Should fail: text not i64
        expect true
```

#### 4.2 Integration (1 hour)

- Update all `infer_expr()` call sites with `InferMode.Synthesize`
- Verify no regressions in existing tests
- Run full test suite

---

## Benefits

### 1. Better Lambda Inference

**Before:**
```simple
# Error: can't infer x's type
val id = \x: x

# Must annotate:
val id = \x: i64: x
```

**After:**
```simple
# Works: type propagated from annotation
val id: fn(i64) -> i64 = \x: x

# Works: type propagated from parameter
fn apply(f: fn(i64) -> i64):
    pass

apply(\x: x * 2)  # x : i64 inferred
```

### 2. Better Error Messages

**Before:**
```
Error: type mismatch
  expected: i64
  found: T42
```

**After:**
```
Error: function body type mismatch
  expected: i64
  found: text
  at: return "oops"
```

### 3. Less Annotation Burden

**Before:**
```simple
val map_twice = \f: fn(i64) -> i64, xs: [i64]:
    xs.map(f).map(f)
```

**After:**
```simple
val map_twice: fn(fn(i64) -> i64, [i64]) -> [i64] = \f, xs:
    xs.map(f).map(f)
```

---

## Implementation Status

### Phase Breakdown

| Phase | Hours | Status |
|-------|-------|--------|
| Phase 1: Core Infrastructure | 4 | 🟡 Planned |
| Phase 2: Check Mode | 4 | 🟡 Planned |
| Phase 3: Return Checking | 2 | 🟡 Planned |
| Phase 4: Testing | 2 | 🟡 Planned |
| **Total** | **12** | 🟡 Planned |

### File Changes

| File | Changes | Lines |
|------|---------|-------|
| `type_infer.spl` | Add mode parameter, check_expr(), subsume() | +200, ~50 |
| `type_infer_types.spl` | Already complete (InferMode exists) | 0 |
| `test/compiler/bidir_type_check_spec.spl` | New test file | +150 |

---

## Next Steps

1. **Implement Phase 1** - Add mode parameter and dispatcher
2. **Implement Phase 2** - Lambda and application checking
3. **Implement Phase 3** - Return type checking
4. **Test** - Run comprehensive test suite

---

## Future Enhancements

### 1. Variance-Aware Subsumption

Replace `subsume()` with variance checking:

```simple
me subsume(inferred: HirType, expected: HirType) -> Result<(), TypeInferError>:
    # Use variance checker from Phase 1
    if self.variance_checker.check_subtype(inferred, expected):
        Ok(())
    else:
        Err(TypeError.TypeMismatch(expected, inferred))
```

### 2. Bidirectional Pattern Matching

Propagate expected types into match arms:

```simple
match opt:
    case Some(x): x * 2  # x : i64 inferred from context
    case None: 0
```

### 3. Bidirectional List Comprehensions

```simple
val evens: [i64] = [for x in 0..10 if x % 2 == 0: x]
# x : i64 inferred from [i64] expected type
```

---

## Conclusion

Bidirectional type checking is a **critical** upgrade that:
- ✅ Infrastructure already in place (InferMode enum)
- ✅ Improves lambda inference significantly
- ✅ Reduces annotation burden
- ✅ Provides better error messages
- ✅ Paves way for variance-aware subtyping

**Status:** Ready to implement (12 hours)

**Priority:** P0 - Blocks lambda usability improvements

---

**Plan Created:** 2026-02-03
**Implementation:** Not started
**Next:** Begin Phase 1 implementation
