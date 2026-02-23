# Codegen Completion Plan - Enable Native Bootstrap

**Date:** 2026-01-30
**Goal:** Complete native code generation features to enable self-hosting bootstrap
**Timeline:** 12-16 weeks
**Status:** In Progress

---

## Executive Summary

Currently, the Simple compiler must run in **interpreter mode** because native codegen is missing critical features used by the compiler itself. This plan details the implementation of these missing features to enable a fully native bootstrap pipeline.

**Current State:**
- ✅ Interpreter mode: Complete, all features supported
- ✅ SMF mode: Complete, bytecode format working
- 🟡 Native mode: 80% complete, missing features block bootstrap

**Blocking Issues:**
1. Static methods - Used throughout compiler (CraneliftModule.new(), etc.)
2. Pipeline operators - Used in driver.spl, type_infer.spl
3. Matrix operations - Used in dimension checking
4. Async/await - Used in parallel compilation
5. Context blocks - Used in error tracking

---

## Phase 1: Static Method Support (Week 1-3)

**Priority:** P0 - Blocks bootstrap immediately

### Current Problem

Static method calls like `Point.origin()` are not properly distinguished from instance methods:

```simple
# Currently fails in native mode:
val p = Point.origin()       # Static method call
val module = CraneliftModule.new_module("main")
```

**Error:**
```
error: Static method `Point.origin()` not yet supported in native compilation.
       Use interpreter mode...
```

### Root Cause Analysis

1. **HIR Representation:** `MethodCall` enum doesn't distinguish static vs instance
   - Current: `MethodCall(receiver: HirExpr, method: text, ...)`
   - Receiver is an expression, not a type reference

2. **Method Resolution:** `MethodResolution` enum has no `StaticMethod` variant
   - Only has: `InstanceMethod`, `TraitMethod`, `FreeFunction`, `Unresolved`
   - Static methods currently resolve as `FreeFunction` (incorrect)

3. **MIR Lowering:** No `CallStatic` instruction
   - All calls use `Call(func, args)` - loses static method distinction

4. **Codegen:** No special handling for static dispatch
   - Tries to load `self` parameter (doesn't exist for static)

### Implementation Plan

#### Step 1.1: Add Static Method to MethodResolution (hir.spl)

```simple
enum MethodResolution:
    InstanceMethod(type_id: SymbolId, method_id: SymbolId)
    TraitMethod(trait_id: SymbolId, method_id: SymbolId)
    FreeFunction(func_id: SymbolId)

    # NEW: Static method on a type (no receiver)
    StaticMethod(type_id: SymbolId, method_id: SymbolId)

    Unresolved
```

**Files:** `simple/compiler/hir.spl:110-123`

#### Step 1.2: Update Parser to Detect Static Calls (parser.spl)

Distinguish `Type.method()` from `expr.method()`:

```simple
# Parse method call
fn parse_method_call(base: Expr) -> Expr:
    # Check if base is a type reference (not an expression)
    val is_static = match base.kind:
        case TypeRef(_): true      # NEW: Type reference
        case Var(name) if self.is_type_name(name): true
        case _: false

    if is_static:
        # Parse as static method call
        ExprKind.StaticCall(type_: base, method: method_name, args: args)
    else:
        # Parse as instance method call
        ExprKind.MethodCall(receiver: base, method: method_name, args: args)
```

**Files:** `simple/compiler/parser.spl:1357`

#### Step 1.3: Add StaticCall to HIR (hir.spl)

```simple
enum HirExprKind:
    # ... existing variants ...

    # Instance method call: receiver.method(args)
    MethodCall(receiver: HirExpr, method: text, args: [HirCallArg], resolution: MethodResolution)

    # NEW: Static method call: Type.method(args)
    StaticCall(type_: HirType, method: text, args: [HirCallArg], resolution: MethodResolution)
```

**Files:** `simple/compiler/hir.spl:714`

#### Step 1.4: Update Method Resolver (resolve.spl)

Add static method resolution logic:

```simple
me resolve_static_call(type_: HirType, method: text) -> MethodResolution:
    """Resolve a static method call Type.method()"""

    val type_sym = self.type_checker.get_type_symbol(type_)
    if not type_sym.?:
        return MethodResolution.Unresolved

    val type_id = type_sym.unwrap()

    # Look for static methods in type definition
    val method_sym = self.symbols.lookup_static_method(type_id, method)

    if method_sym.?:
        MethodResolution.StaticMethod(type_id, method_sym.unwrap())
    else:
        self.add_error("no static method '{method}' found for type '{type_.kind}'", span)
        MethodResolution.Unresolved
```

**Files:** `simple/compiler/resolve.spl:500-544`

#### Step 1.5: Add CallStatic to MIR (mir.spl)

```simple
enum MirInstKind:
    # ... existing instructions ...

    Call(dest: LocalId?, func: MirOperand, args: [MirOperand])

    # NEW: Static method call - no receiver, direct dispatch
    CallStatic(dest: LocalId?, type_id: SymbolId, method_id: SymbolId, args: [MirOperand])
```

**Files:** `simple/compiler/mir.spl:200-250`

#### Step 1.6: Update MIR Lowering (mir.spl HIR→MIR section)

```simple
fn lower_expr(expr: HirExpr) -> LocalId:
    match expr.kind:
        # ... existing cases ...

        case StaticCall(type_, method, args, resolution):
            match resolution:
                case StaticMethod(type_id, method_id):
                    val dest = self.alloc_temp()
                    val arg_locals = args.map(\a: self.lower_expr(a.value))
                    self.emit(MirInstKind.CallStatic(dest, type_id, method_id, arg_locals))
                    dest
                case _:
                    self.error("unresolved static method call")
                    self.alloc_temp()  # Error recovery
```

**Files:** `simple/compiler/mir.spl:1000-1050`

#### Step 1.7: Implement Codegen for CallStatic (codegen.spl)

```simple
me compile_inst(inst: MirInst):
    match inst.kind:
        # ... existing cases ...

        case CallStatic(dest, type_id, method_id, args):
            # Get the static method's function ID
            val func_name = self.get_static_method_name(type_id, method_id)
            val func_id = self.function_map[func_name]

            # Compile arguments (no receiver!)
            var arg_values: [i64] = []
            for arg in args:
                arg_values = arg_values.push(self.compile_operand(arg))

            # Direct call (no dynamic dispatch)
            val result = rt_cranelift_call(
                self.current_ctx,
                func_id,
                arg_values.ptr(),
                arg_values.len()
            )

            if dest.?:
                self.local_values[dest.unwrap().id] = result
```

**Files:** `simple/compiler/codegen.spl:345-445`

#### Step 1.8: Add Rust FFI Support (if needed)

Check if any Rust codegen changes are needed in `src/rust/compiler/src/codegen/`.

**Files:** `src/rust/compiler/src/codegen/instr/*.rs`

#### Step 1.9: Write SSpec Tests

Create comprehensive tests for static methods:

```simple
# test/lib/std/unit/codegen/static_method_spec.spl

feature "Static Method Codegen":
    it "compiles simple static method":
        val code = """
        class Point:
            x: i64
            y: i64

            static fn origin() -> Point:
                Point(x: 0, y: 0)

        fn main() -> i64:
            val p = Point.origin()
            p.x + p.y
        """

        # Test in all 3 modes
        expect compile_and_run_interpreter(code, "main", []).to_equal(0)
        expect compile_and_run_smf(code, "main", []).to_equal(0)
        expect compile_and_run_native(code, "main", []).to_equal(0)

    it "compiles static method with parameters":
        val code = """
        class Rectangle:
            width: i64
            height: i64

            static fn square(size: i64) -> Rectangle:
                Rectangle(width: size, height: size)

        fn main() -> i64:
            val r = Rectangle.square(5)
            r.width * r.height
        """

        expect compile_and_run_native(code, "main", []).to_equal(25)

    it "compiles chained static method calls":
        val code = """
        class Builder:
            static fn new() -> Builder:
                Builder()

            fn build() -> i64:
                42

        fn main() -> i64:
            Builder.new().build()
        """

        expect compile_and_run_native(code, "main", []).to_equal(42)

    slow_it "stress test 1000 static method calls":
        # Performance test
        val code = """
        class Counter:
            static fn increment(x: i64) -> i64:
                x + 1

        fn main() -> i64:
            var result = 0
            for i in 0..1000:
                result = Counter.increment(result)
            result
        """

        expect compile_and_run_native(code, "main", []).to_equal(1000)
```

**Files:**
- `test/lib/std/unit/codegen/static_method_spec.spl` (new)
- `simple/std_lib/test/features/static_method_codegen_spec.spl` (new)

### Success Criteria

- [ ] All existing static method tests pass in native mode
- [ ] Bootstrap compiler uses `Point.origin()` and similar patterns successfully
- [ ] No performance regression (static dispatch should be faster than dynamic)
- [ ] 100% test coverage for static method edge cases

### Estimated Effort

**3 weeks** (1 engineer):
- Week 1: HIR/MIR changes (Steps 1.1-1.6)
- Week 2: Codegen implementation (Steps 1.7-1.8)
- Week 3: Testing and debugging (Step 1.9)

---

## Phase 2: Pipeline Operators (Week 4-7)

**Priority:** P0 - Used extensively in compiler

### Missing Operators

1. `|>` - Pipe forward: `x |> f` = `f(x)`
2. `>>` - Forward composition: `f >> g` = `λx. g(f(x))`
3. `<<` - Backward composition: `f << g` = `λx. f(g(x))`
4. `//` - Parallel execution: `f // g` = run `f` and `g` concurrently
5. `~>` - Layer connect: NN layer composition with dimension checking

### Current Problem

```simple
# Currently fails in native mode:
val processed = data |> normalize |> transform |> predict
val pipeline = normalize >> augment >> to_tensor
val model = Linear(784, 256) ~> ReLU() ~> Linear(256, 10)
```

**Error:**
```
error: Pipe forward (|>) requires interpreter mode for function dispatch
```

### Implementation Plan

#### Step 2.1: Add Runtime Function Dispatch Support

Pipeline operators need runtime function values. Currently, functions are compile-time only.

**Add to runtime:**

```rust
// src/rust/runtime/src/value/function.rs (new file)

pub struct RuntimeFunction {
    func_ptr: FunctionPointer,
    closure_data: Option<Box<[RuntimeValue]>>,
    signature: FunctionSignature,
}

#[no_mangle]
pub extern "C" fn rt_function_call(
    func: RuntimeValue,
    args: RuntimeValue,
) -> RuntimeValue {
    // Dispatch to function pointer with arguments
}

#[no_mangle]
pub extern "C" fn rt_function_compose(
    f: RuntimeValue,
    g: RuntimeValue,
) -> RuntimeValue {
    // Create new function: λx. g(f(x))
}
```

#### Step 2.2: Update MIR for Pipeline Ops

```simple
enum MirInstKind:
    # Add pipeline instructions
    PipeForward(dest: LocalId, value: MirOperand, func: MirOperand)
    Compose(dest: LocalId, f: MirOperand, g: MirOperand, kind: ComposeKind)
    Parallel(dest: LocalId, funcs: [MirOperand])
```

#### Step 2.3: Implement Codegen

```simple
me compile_inst(inst: MirInst):
    match inst.kind:
        case PipeForward(dest, value, func):
            val v = self.compile_operand(value)
            val f = self.compile_operand(func)

            # Call runtime function dispatcher
            val call_id = self.runtime_funcs["rt_function_call"]
            val call_ref = self.module.declare_func_in_func(call_id, self.current_ctx)
            val result = rt_cranelift_call(call_ref, [f, v])
            self.local_values[dest.id] = result

        case Compose(dest, f, g, kind):
            val f_val = self.compile_operand(f)
            val g_val = self.compile_operand(g)

            val compose_id = self.runtime_funcs["rt_function_compose"]
            val result = rt_cranelift_call(compose_id, [f_val, g_val])
            self.local_values[dest.id] = result
```

**Files:** `simple/compiler/codegen.spl:345-445`

#### Step 2.4: Write SSpec Tests

```simple
feature "Pipeline Operator Codegen":
    it "compiles pipe forward":
        val code = """
        fn double(x: i64) -> i64: x * 2
        fn add_ten(x: i64) -> i64: x + 10

        fn main() -> i64:
            5 |> double |> add_ten
        """

        expect compile_and_run_native(code, "main", []).to_equal(20)

    it "compiles function composition":
        val code = """
        fn double(x: i64) -> i64: x * 2
        fn add_ten(x: i64) -> i64: x + 10

        fn main() -> i64:
            val f = double >> add_ten
            f(5)
        """

        expect compile_and_run_native(code, "main", []).to_equal(20)
```

### Estimated Effort

**4 weeks** (1 engineer):
- Week 4: Runtime function value support
- Week 5-6: MIR + Codegen for |>, >>, <<
- Week 7: Parallel (//) and layer connect (~>)

---

## Phase 3: Matrix Operations (Week 8-11)

**Priority:** P1 - Used in dimension checking

### Missing Features

1. `@` - Matrix multiplication
2. `.+`, `.-`, `.*`, `./`, `.^` - Element-wise broadcasting

### Implementation Plan

#### Step 3.1: Add Matrix Runtime Library

**Option A:** BLAS/LAPACK FFI (recommended)
```rust
// src/rust/matrix/src/lib.rs (new crate)

use openblas_src::*;

#[no_mangle]
pub extern "C" fn rt_matrix_mul(
    a: RuntimeValue,
    b: RuntimeValue,
) -> RuntimeValue {
    // Call BLAS dgemm
}
```

**Option B:** Custom implementation (fallback)
```rust
#[no_mangle]
pub extern "C" fn rt_matrix_mul_naive(
    a: RuntimeValue,
    b: RuntimeValue,
) -> RuntimeValue {
    // Triple nested loop (slow but works)
}
```

#### Step 3.2: Add Dimension Checking at Compile Time

Use existing dimension inference system:

```simple
# In type_infer.spl
fn check_matmul_dimensions(left_type: HirType, right_type: HirType) -> Result<HirType, TypeError>:
    match (left_type.kind, right_type.kind):
        case (Array(_, [m, k1]), Array(_, [k2, n])):
            if k1 != k2:
                return Err(TypeError.DimensionMismatch(
                    "matrix multiplication dimension mismatch: [{m}, {k1}] @ [{k2}, {n}]"
                ))
            Ok(HirType.array([m, n]))
        case _:
            Err(TypeError.NotMatrixType)
```

#### Step 3.3: Implement Codegen

```simple
me compile_binop(op: MirBinOp, left: i64, right: i64) -> i64:
    match op:
        case MatMul:
            val matmul_id = self.runtime_funcs["rt_matrix_mul"]
            val matmul_ref = self.module.declare_func_in_func(matmul_id, self.current_ctx)
            rt_cranelift_call(matmul_ref, [left, right])

        case BroadcastAdd:
            val broadcast_id = self.runtime_funcs["rt_array_broadcast_add"]
            rt_cranelift_call(broadcast_id, [left, right])
```

**Files:** `simple/compiler/codegen.spl:479-517`

### Estimated Effort

**4 weeks** (1 engineer):
- Week 8: Matrix runtime library (BLAS integration)
- Week 9: Dimension checking integration
- Week 10: Codegen implementation
- Week 11: Testing and optimization

---

## Phase 4: Async/Await (Week 12-15)

**Priority:** P1 - Used in parallel compilation

### Implementation Plan

#### Step 4.1: Integrate Tokio Runtime

```rust
// src/rust/async_runtime/src/lib.rs (new crate)

use tokio::runtime::Runtime;

#[no_mangle]
pub extern "C" fn rt_async_spawn(
    func: RuntimeValue,
    args: RuntimeValue,
) -> RuntimeValue {
    // Spawn on tokio runtime
}

#[no_mangle]
pub extern "C" fn rt_async_await(
    future: RuntimeValue,
) -> RuntimeValue {
    // Block on future
}
```

#### Step 4.2: Add Async Instructions to MIR

```simple
enum MirInstKind:
    # Async operations
    Await(dest: LocalId, future: MirOperand)
    Spawn(dest: LocalId, func: MirOperand, args: [MirOperand])
```

#### Step 4.3: Implement Codegen

```simple
me compile_inst(inst: MirInst):
    match inst.kind:
        case Await(dest, future):
            val future_val = self.compile_operand(future)
            val await_id = self.runtime_funcs["rt_async_await"]
            val result = rt_cranelift_call(await_id, [future_val])
            self.local_values[dest.id] = result
```

### Estimated Effort

**4 weeks** (1 engineer)

---

## Phase 5: Context Blocks (Week 16)

**Priority:** P2 - Nice to have

### Implementation Plan

Add context tracking to runtime, similar to Python's context managers.

### Estimated Effort

**1 week** (1 engineer)

---

## Testing Strategy

### Test Coverage Requirements

Each feature must have:

1. **Unit tests** - Test MIR lowering, codegen in isolation
2. **Integration tests** - Test full compilation pipeline
3. **SSpec feature tests** - Executable specification
4. **Bootstrap verification** - Ensure compiler can compile itself

### Test Modes

All tests must pass in **all 3 execution modes:**

1. ✅ Interpreter mode (baseline - already works)
2. ✅ SMF mode (bytecode)
3. ✅ Native mode (new - target of this plan)

### Regression Prevention

- Run full test suite before/after each phase
- No feature complete until 100% test pass rate
- Performance benchmarks to catch slowdowns

---

## Timeline Summary

| Phase | Weeks | Priority | Blocking | Effort (engineer-weeks) |
|-------|-------|----------|----------|------------------------|
| Static Methods | 1-3 | P0 | ✅ Blocks bootstrap | 3 |
| Pipeline Operators | 4-7 | P0 | ✅ Blocks bootstrap | 4 |
| Matrix Operations | 8-11 | P1 | ⚠️ Used in compiler | 4 |
| Async/Await | 12-15 | P1 | ⚠️ Used in compiler | 4 |
| Context Blocks | 16 | P2 | ❌ Optional | 1 |
| **Total** | **16 weeks** | | | **16 engineer-weeks** |

**Critical path:** Phases 1-2 (Static methods + Pipelines) - 7 weeks

**Minimum viable bootstrap:** Complete Phases 1-2 only (Week 7)

---

## Success Metrics

### Phase 1-2 Completion (Week 7)

- [ ] Compiler compiles itself in native mode (no interpreter!)
- [ ] `simple_new1` → `simple_new2` → `simple_new3` all use native codegen
- [ ] Bootstrap time reduced from ~45s to ~15s (3x speedup)
- [ ] All 631+ tests pass in native mode

### Full Completion (Week 16)

- [ ] All codegen features implemented
- [ ] 100% feature parity with interpreter
- [ ] Bootstrap time <10s (5x faster than interpreter)
- [ ] Native performance within 10% of hand-written Rust

---

## Risks and Mitigation

### Risk 1: BLAS Dependency Complexity

**Impact:** High - Matrix ops blocked
**Probability:** Medium
**Mitigation:**
- Implement naive fallback first (week 8)
- Add BLAS optimization later (week 10-11)
- Provide compile-time flag to disable BLAS

### Risk 2: Async Runtime Integration Complexity

**Impact:** Medium - Parallel compilation slower
**Probability:** Medium
**Mitigation:**
- Use existing Tokio integration from Rust runtime
- Start with simple spawn/await (no advanced features)
- Can defer to v0.5.0 if needed

### Risk 3: Testing Burden

**Impact:** High - Quality assurance
**Probability:** Low (we have good test infrastructure)
**Mitigation:**
- Write tests incrementally alongside implementation
- Automate test generation where possible
- Use property-based testing for edge cases

---

## Dependencies

### External Crates (Rust)

- `cranelift-codegen` - Already integrated ✅
- `openblas-src` - Matrix operations (Phase 3)
- `tokio` - Async runtime (Phase 4) - Already integrated ✅

### Internal Modules

- `simple/compiler/hir.spl` - HIR definitions
- `simple/compiler/mir.spl` - MIR definitions
- `simple/compiler/codegen.spl` - Code generation
- `simple/compiler/resolve.spl` - Method resolution
- `src/rust/runtime/` - Runtime support functions

---

## Next Steps

1. **Immediate (Week 1):** Start Phase 1 - Static method support
2. **Review (Week 4):** After Phase 1, review progress and adjust timeline
3. **Checkpoint (Week 7):** Demo native bootstrap working
4. **Final review (Week 16):** All features complete, documentation updated

---

## Appendix A: Alternative Approaches

### Hybrid Compilation (Considered but deferred)

Instead of completing all features, compile safe subset natively and interpret advanced features.

**Pros:**
- Faster time to partial bootstrap (4 weeks vs 7 weeks)
- Lower risk

**Cons:**
- Still relies on interpreter for 20% of code
- Only 3-5x speedup (vs 10x with full native)
- Defers problem rather than solving it

**Decision:** Implement full native support now (cleaner long-term)

### LLVM Backend (Future v1.0+)

Replace Cranelift with LLVM IR generation.

**Pros:**
- Better optimization
- More mature toolchain

**Cons:**
- 20-30 weeks effort
- LLVM dependency is heavy

**Decision:** Defer to v1.0.0, complete Cranelift backend first

---

## Appendix B: Performance Targets

| Metric | Interpreter | Target (Native) | Notes |
|--------|-------------|-----------------|-------|
| Bootstrap time (3-stage) | ~45s | <10s | 5x faster |
| Compiler throughput | ~500 LOC/s | ~2500 LOC/s | 5x faster |
| Memory usage | ~200MB | ~100MB | 2x reduction |
| Binary size | ~80MB | ~60MB | Smaller (no interpreter) |

---

**End of Codegen Completion Plan**
