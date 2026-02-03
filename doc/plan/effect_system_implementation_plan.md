# Effect System Implementation Plan (Phase 3)

**Date:** 2026-02-03
**Priority:** P2
**Estimated Effort:** 20 hours
**Status:** Ready to implement

---

## Overview

Implement automatic async/sync effect inference for Simple's compiler, leveraging existing suspension operators (`~`, `~=`, `if~`, `while~`, `for~`).

**Goal:** Functions automatically inferred as async if they contain suspension points, without requiring explicit `async fn` annotations.

---

## Current Limitations

Simple currently has no effect tracking:

```simple
fn fetch_data():          # Unknown if async
    val url = get_url()   # Unknown if suspends
    http.get(url)         # Is this async?
```

**Problems:**
- Can't distinguish sync from async functions
- Promise types not inferred
- No validation of suspension points
- Can't verify `fn sync` annotations

---

## Design

### Effect Model

```simple
enum Effect:
    Sync    # Returns T directly
    Async   # Returns Promise<T>

class EffectEnv:
    # Function symbol → inferred effect
    effects: Dict<Symbol, Effect>

    # Built-in effect annotations
    builtins: Dict<Symbol, Effect>
```

### Suspension Operators (Already in Parser)

| Operator | Meaning | Effect |
|----------|---------|--------|
| `~expr` | Suspend/await | Forces Async |
| `~=` | Suspend assign | Forces Async |
| `if~` | Suspend if | Forces Async |
| `while~` | Suspend while | Forces Async |
| `for~` | Suspend for | Forces Async |

### Inference Algorithm

**Fixed-point iteration:**

```
1. Initialize all functions as Sync
2. Mark built-in async functions (FFI)
3. Repeat until no changes:
   a. For each function:
      - Scan body for suspension operators → Async
      - Scan calls to async functions → Async
   b. If function's effect changed, mark dirty
4. Update return types: Async functions return Promise<T>
```

---

## Implementation Phases

### Phase 3A: Effect Types & Infrastructure (5 hours)

**New file:** `src/compiler/effects.spl`

```simple
enum Effect:
    Sync
    Async

    fn to_string() -> text:
        match self:
            case Sync: "sync"
            case Async: "async"

    fn is_async() -> bool:
        match self:
            case Async: true
            case _: false

class EffectEnv:
    # Function symbol → effect
    effects: Dict<Symbol, Effect>

    # Built-in annotations (FFI)
    builtins: Dict<Symbol, Effect>

    fn new() -> EffectEnv:
        EffectEnv(
            effects: {},
            builtins: init_builtins()
        )

    fn get_effect(sym: Symbol) -> Effect:
        # Check local effects first, then builtins
        self.effects.get(sym).or_else(
            self.builtins.get(sym).or_else(Effect.Sync)
        )

    fn set_effect(sym: Symbol, eff: Effect):
        self.effects[sym] = eff

    fn init_builtins() -> Dict<Symbol, Effect>:
        # Mark known async FFI functions
        {
            "http.get": Effect.Async,
            "http.post": Effect.Async,
            "file.read_async": Effect.Async,
            "sleep": Effect.Async,
            # Add more as needed
        }
```

**Tests:**
- Effect enum creation
- EffectEnv initialization
- Built-in lookup
- Effect setting/getting

**Estimate:** 5 hours

---

### Phase 3B: Body Scanning (6 hours)

**Extend:** `src/compiler/effects.spl`

```simple
class EffectScanner:
    env: EffectEnv

    fn scan_function(func: HirFunction) -> Effect:
        # Scan body for suspension points
        self.scan_expr(func.body)

    fn scan_expr(expr: HirExpr) -> Effect:
        match expr:
            # Suspension operators
            case Suspend(_):        Effect.Async
            case SuspendAssign(_):  Effect.Async
            case SuspendIf(_):      Effect.Async
            case SuspendWhile(_):   Effect.Async
            case SuspendFor(_):     Effect.Async

            # Function calls - check callee's effect
            case Call(func, args):
                val callee_eff = self.env.get_effect(func.symbol)
                if callee_eff.is_async():
                    Effect.Async
                else:
                    # Recurse into arguments
                    self.scan_exprs(args)

            # Binary/unary ops - recurse
            case Binary(lhs, op, rhs):
                val left_eff = self.scan_expr(lhs)
                val right_eff = self.scan_expr(rhs)
                self.combine_effects(left_eff, right_eff)

            # Control flow - recurse
            case If(cond, then, else_):
                val cond_eff = self.scan_expr(cond)
                val then_eff = self.scan_expr(then)
                val else_eff = else_.map(\e: self.scan_expr(e))
                    .or_else(Effect.Sync)
                self.combine_effects(cond_eff, then_eff, else_eff)

            # Block - scan all statements
            case Block(stmts):
                self.scan_stmts(stmts)

            # Match - scan all arms
            case Match(scrutinee, arms):
                val scrutinee_eff = self.scan_expr(scrutinee)
                val arms_eff = arms.map(\arm: self.scan_expr(arm.body))
                self.combine_effects([scrutinee_eff] + arms_eff)

            # Literals, variables - always Sync
            _: Effect.Sync

    fn combine_effects(effs: [Effect]) -> Effect:
        # If any is Async, result is Async
        effs.any(\e: e.is_async())
            .then(Effect.Async)
            .or_else(Effect.Sync)
```

**Tests:**
- Scan function with `~` operator
- Scan function with async call
- Scan nested control flow
- Scan match expressions
- Verify sync function stays sync

**Estimate:** 6 hours

---

### Phase 3C: Fixed-Point Solver (5 hours)

**Extend:** `src/compiler/effects.spl`

```simple
class EffectSolver:
    env: EffectEnv
    scanner: EffectScanner

    fn solve(functions: [HirFunction]) -> EffectEnv:
        # Initialize all as Sync
        for func in functions:
            self.env.set_effect(func.symbol, Effect.Sync)

        # Fixed-point iteration
        var changed = true
        var iterations = 0
        val max_iterations = 100  # Prevent infinite loop

        while changed and iterations < max_iterations:
            changed = false
            iterations = iterations + 1

            for func in functions:
                val old_effect = self.env.get_effect(func.symbol)
                val new_effect = self.scanner.scan_function(func)

                if new_effect != old_effect:
                    self.env.set_effect(func.symbol, new_effect)
                    changed = true

        if iterations == max_iterations:
            print "Warning: Effect solver reached max iterations"

        self.env

    fn verify_annotations(functions: [HirFunction]) -> [EffectError]:
        # Check explicit `fn sync` annotations
        var errors = []

        for func in functions:
            if func.is_annotated_sync():
                val inferred = self.env.get_effect(func.symbol)
                if inferred.is_async():
                    errors.push(EffectError(
                        message: "Function annotated as sync but contains async operations",
                        function: func.symbol,
                        span: func.span
                    ))

        errors
```

**Tests:**
- Single function inference
- Two mutually-calling functions
- Deep call chain (A → B → C, C is async)
- Cycle detection
- Verify `fn sync` annotation checking

**Estimate:** 5 hours

---

### Phase 3D: Promise Type Wrapping (4 hours)

**Extend:** `src/compiler/type_infer.spl`

```simple
# In TypeInferrer class

fn infer_function_return_type(func: HirFunction) -> HirType:
    # Infer body type
    val body_ty = self.infer_expr(func.body, None)?

    # Check if function is async
    val effect = self.effect_env.get_effect(func.symbol)

    match effect:
        case Effect.Async:
            # Wrap in Promise<T>
            HirType.Generic(
                name: "Promise",
                args: [body_ty]
            )
        case Effect.Sync:
            body_ty

fn check_suspension_operator(expr: HirExpr) -> Result<HirType, TypeInferError>:
    # ~expr operator
    match expr:
        case Suspend(inner):
            # Infer inner expression type
            val inner_ty = self.infer_expr(inner, None)?

            # Must be Promise<T>
            match inner_ty:
                case Generic("Promise", [elem_ty]):
                    # Unwrap promise: Promise<T> → T
                    Ok(elem_ty)
                case _:
                    Err(TypeInferError(
                        message: "Suspend operator requires Promise type",
                        expected: "Promise<T>",
                        found: inner_ty.to_string(),
                        span: expr.span
                    ))
```

**Tests:**
- Async function returns Promise<T>
- Sync function returns T
- Suspend operator unwraps Promise
- Error on suspend non-promise
- Nested promises: Promise<Promise<T>>

**Estimate:** 4 hours

---

## Integration with Compiler

### Compilation Pipeline

```
1. Parse → AST
2. Lower → HIR
3. [NEW] Effect Inference → EffectEnv
4. Type Inference (with EffectEnv)
5. Borrow Check
6. Lower → MIR
7. Codegen
```

**Modification:** `src/compiler/mod.spl`

```simple
fn compile_module(ast: Ast) -> Result<Module, CompileError>:
    # Existing phases
    val hir = lower_to_hir(ast)?

    # NEW: Effect inference
    val effect_env = infer_effects(hir)?

    # Type inference (pass effect_env)
    val typed_hir = type_check(hir, effect_env)?

    # Continue with existing phases
    val mir = lower_to_mir(typed_hir)?
    val module = codegen(mir)?

    Ok(module)
```

---

## Testing Strategy

### Unit Tests (40 tests)

| Category | Count | Examples |
|----------|-------|----------|
| Effect types | 5 | Enum, EffectEnv creation |
| Body scanning | 15 | Suspension ops, calls, control flow |
| Fixed-point solver | 10 | Convergence, cycles, annotations |
| Promise wrapping | 10 | Return types, unwrapping |

### Integration Tests (10 tests)

```simple
# Test 1: Simple async function
fn async_fetch():
    val response = ~http.get("https://api.example.com")
    response.body

# Expected: Effect.Async, returns Promise<String>

# Test 2: Sync function calling async
fn wrapper():
    val result = ~async_fetch()
    result

# Expected: Effect.Async (propagated), returns Promise<String>

# Test 3: Sync function (no suspension)
fn pure_calc():
    42 + 58

# Expected: Effect.Sync, returns Int

# Test 4: Error on sync annotation violation
fn sync incorrect_annotation():
    ~async_fetch()  # ERROR: Marked sync but contains suspension

# Expected: EffectError
```

### Regression Tests (5 tests)

- Verify existing sync code still works
- No performance regression on sync functions
- Backward compatibility with existing codebase

**Total Tests:** 55+

---

## File Structure

```
src/compiler/
├── effects.spl              [NEW] Effect inference (500 lines)
│   ├── Effect enum
│   ├── EffectEnv class
│   ├── EffectScanner class
│   └── EffectSolver class
├── type_infer.spl          [MODIFY] Promise wrapping (+50 lines)
├── mod.spl                 [MODIFY] Pipeline integration (+10 lines)

test/compiler/
├── effects_spec.spl         [NEW] Unit tests (40 tests)
└── integration/
    └── async_effects_spec.spl [NEW] Integration tests (15 tests)
```

---

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| 3A: Infrastructure | 5h | Effect types, EffectEnv |
| 3B: Body scanning | 6h | EffectScanner |
| 3C: Solver | 5h | EffectSolver, fixed-point |
| 3D: Promise wrapping | 4h | Type integration |
| **Total** | **20h** | **Complete effect system** |

**Recommended Schedule:** 2.5 days full-time or 5 days half-time

---

## Success Criteria

✅ Effect system is complete when:

1. **Functionality**
   - Functions with `~` automatically marked Async
   - Fixed-point solver converges on call graphs
   - Promise types correctly inferred for async functions
   - `fn sync` annotations validated

2. **Testing**
   - 55+ tests passing
   - All unit tests pass
   - Integration tests demonstrate real-world usage
   - No regression in existing sync code

3. **Performance**
   - Effect inference adds <5% to compilation time
   - Fixed-point solver converges in <10 iterations typical
   - No runtime overhead for sync functions

4. **Documentation**
   - Implementation guide in doc/design/
   - API documentation for EffectEnv
   - Examples in doc/examples/effects/

---

## Benefits

**User Experience:**
- No need for explicit `async fn` annotations
- Automatic promise wrapping
- Clear async/sync distinction
- Better error messages (suspension in sync context)

**Compiler:**
- Foundation for async optimization
- Call graph analysis
- Enables generator desugaring
- Supports async/await lowering

**Type System:**
- Promise types automatically inferred
- Effect polymorphism possible (future)
- Better error reporting for type mismatches

---

## Risks & Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Fixed-point doesn't converge | Low | High | Max iteration limit, cycle detection |
| Performance overhead | Medium | Medium | Profile early, optimize scanner |
| Integration complexity | Medium | High | Incremental integration, feature flag |
| Test coverage gaps | Low | Medium | Comprehensive test plan, reviews |

---

## Future Extensions (Out of Scope)

After Phase 3 complete, consider:

1. **Effect Polymorphism** (10h)
   - `fn identity<E>(x: T) -> T with E` - polymorphic in effect

2. **Generator Lowering** (15h)
   - Desugar suspension operators to state machines

3. **Async Optimization** (8h)
   - Elide Promise allocation for tail calls
   - Inline small async functions

4. **Effect Subtyping** (6h)
   - Sync <: Async (sync can be used where async expected)

**Total Future Work:** 39 hours (optional)

---

## References

- **Rust Implementation:** `rust/type/src/effects.rs` (1,500 lines)
- **Design Document:** `doc/design/effect_system_design.md` (to be created)
- **Roadmap:** `doc/plan/rust_feature_parity_roadmap.md` (Phase 3)

---

**Status:** Ready to implement
**Next Step:** Phase 3A - Effect Types & Infrastructure
**Estimated Completion:** 2026-02-06 (3 days from now)
