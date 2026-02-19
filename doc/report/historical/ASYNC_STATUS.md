# Async/Await Implementation Status

**Date:** 2026-02-11
**Overall Status:** 🟡 Parser Complete, Runtime Partial

## Summary

Async/await syntax is now fully parseable and has basic interpreter support. The language can recognize and parse `async fn`, `await`, `yield`, and `spawn` without errors. However, full async execution requires additional integration work.

## ✅ Completed

### 1. Parser Support (COMPLETE)
- **Tokens:** TOK_KW_ASYNC, TOK_KW_AWAIT, TOK_KW_YIELD, TOK_KW_SPAWN
- **AST Nodes:** EXPR_AWAIT, EXPR_YIELD, EXPR_SPAWN, EXPR_ASYNC_BLOCK
- **Declaration Support:** `decl_is_async` array tracks async functions
- **Parsing Logic:** `async fn name()` declarations, `await expr`, `yield expr`, `spawn expr`
- **Expression Constructors:** `expr_await()`, `expr_yield()`, `expr_spawn()`

**Files Modified:**
- `src/compiler_core/tokens.spl` - Added async tokens
- `src/compiler_core/ast.spl` - Added async AST support
- `src/compiler_core/parser.spl` - Added async parsing logic

### 2. Basic Interpreter Integration (STUBS)
- **Evaluators:** `eval_await_expr()`, `eval_yield_expr()`, `eval_spawn_expr()`
- **Behavior:** Currently evaluate synchronously (no state machine)
- **Purpose:** Prevent crashes, allow code to run

**Files Modified:**
- `src/compiler_core/interpreter/eval.spl` - Added async expression evaluators

### 3. Testing
- ✅ Parser accepts async syntax without errors
- ✅ Async functions can be called (return Promise objects)
- ⚠️ Await expression fails at runtime ("requires Future or Actor handle")

## ⏳ In Progress / TODO

### 4. Desugar Pipeline Integration
**Problem:** Two separate AST systems exist:
- `core.ast` (arena-based) - What the parser produces
- `compiler.parser_types` (struct-based) - What the desugar pipeline uses

**Solution Needed:**
- Create AST conversion layer, OR
- Unify AST representations, OR
- Port desugar to work with core.ast

**Desugar Pipeline Components** (Already Exist):
- `src/compiler/desugar/suspension_analysis.spl` - Find await points
- `src/compiler/desugar/state_enum.spl` - Generate state machine
- `src/compiler/desugar/poll_generator.spl` - Generate poll function

### 5. Runtime Async Support
**Current Situation:**
- Async runtime exists at `src/std/async/` (Promise, Future, Task, Executor)
- Runtime uses generics heavily (Promise<T>, Future<T>)
- **Runtime Limitation:** Generics don't work in interpreter
- Async functions return raw Promise objects
- Await cannot properly handle these Promises

**Solutions:**
1. **State Machine Execution:** Transform async functions to state machines and execute in interpreter
2. **Native Compilation:** Compile async functions to C, skip interpreter
3. **Runtime-Safe Async:** Create non-generic async primitives for interpreter

### 6. Test Enablement
**Status:** 591 skip_it annotations remain, including ~70+ async tests

**Async Tests Location:**
- `test/feature/async_features_spec.spl` - 28 skipped
- `test/unit/std/async_spec.spl` - 10 skipped
- `test/unit/std/async_host_spec.spl` - 47 skipped
- `test/unit/std/async_embedded_spec.spl` - 28 skipped
- And more...

**Blockers:**
- Need desugar integration OR
- Need state machine interpreter support OR
- Need compiled async support

## Architecture Notes

### Three Layers of Async Support

1. **Parser Layer** (✅ DONE)
   - Recognizes syntax
   - Builds AST
   - Located: `src/compiler_core/parser.spl`, `src/compiler_core/ast.spl`

2. **Transform Layer** (⏳ TODO)
   - Converts async functions to state machines
   - Currently disconnected from parser
   - Located: `src/compiler/desugar/`
   - Uses: `compiler.parser_types` (different AST)

3. **Runtime Layer** (⚠️ PARTIAL)
   - Executes async code
   - Located: `src/std/async/`, `src/compiler_core/interpreter/eval.spl`
   - Issue: Uses generics (interpreter limitation)

### Why Await Fails

```simple
async fn get_value() -> i64:
    42

val result = await get_value()  # Fails here
```

**What Happens:**
1. `get_value()` is called → returns raw Promise object
2. `await` expression tries to handle Promise
3. `eval_await_expr()` just evaluates the Promise synchronously
4. Promise object is returned as-is
5. Runtime expects Future/Actor handle, gets object → ERROR

**What Should Happen:**
1. `get_value()` transformed to state machine at compile time
2. State machine has poll() method
3. `await` calls poll() until Ready
4. Result value extracted and returned

## Dependencies & Blockers

### Desugar Integration Blockers
- [ ] AST conversion layer between core.ast and compiler.parser_types
- [ ] Compiler driver integration point
- [ ] Generic-free desugar pipeline OR generic support in interpreter

### Runtime Execution Blockers
- [ ] State machine interpreter execution
- [ ] Non-generic Future/Promise types for runtime
- [ ] Poll mechanism in interpreter

### Test Enablement Blockers
- [ ] One of: desugar integration, state machine support, OR native compilation
- [ ] Async runtime that works in interpreter (no generics)

## Recommendations

### Short Term (Enable Basic Async)
1. Create minimal AST conversion (core.ast → compiler.parser_types)
2. Integrate desugar pipeline into build flow
3. Compile async functions to C (bypass interpreter limitation)
4. Enable ~20-30 basic async tests

### Medium Term (Full Interpreter Support)
1. Create runtime-safe async primitives (no generics)
2. Implement state machine execution in interpreter
3. Enable remaining async tests

### Long Term (Full Feature Support)
1. Unify AST representations
2. Generic support in interpreter OR type-erased runtime
3. Full async/await feature parity with compiled code

## Files Reference

**Parser & AST:**
- `src/compiler_core/tokens.spl`
- `src/compiler_core/ast.spl`
- `src/compiler_core/parser.spl`

**Interpreter:**
- `src/compiler_core/interpreter/eval.spl`

**Desugar Pipeline:**
- `src/compiler/desugar/mod.spl`
- `src/compiler/desugar/suspension_analysis.spl`
- `src/compiler/desugar/state_enum.spl`
- `src/compiler/desugar/poll_generator.spl`

**Async Runtime:**
- `src/std/async/__init__.spl`
- `src/std/async/promise.spl`
- `src/std/async/future.spl`
- `src/std/async/task.spl`
- `src/std/async/executor.spl`
- `src/std/async/runtime.spl`

**Documentation:**
- `ASYNC_PARSER_IMPLEMENTATION.md` - Parser implementation details
- `IMPLEMENTATION_SUMMARY.md` - Overall progress
- `ASYNC_STATUS.md` - This file

---

*Parser and basic interpreter stubs complete. Desugar integration and full runtime support required for production use.*
