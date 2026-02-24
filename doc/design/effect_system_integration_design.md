# Effect System Integration with Type Inference Engine

**Status:** Design Document (Research Phase)
**Date:** 2026-02-24
**Author:** Claude Opus 4.6

---

## 1. Current State

### 1.1 What Exists

The Simple compiler has significant effect system infrastructure scattered across multiple layers, but these pieces are not wired together into a cohesive pipeline. Here is an inventory of what exists today.

#### Core Effect Definitions (Four Separate Copies)

There are at least four independent `Effect` enums, each in a different module, each with overlapping but incompatible definitions:

| File | Effect Variants | Scope |
|------|----------------|-------|
| `src/compiler/00.common/effects.spl` | `Sync`, `Async` | Standalone module with `EffectEnv`, `EffectError`, `EffectStats`. Uses `type Symbol = text` placeholders. |
| `src/compiler/00.common/effects_v1_simple.spl` | `Sync`, `Async` | Phase 3A copy -- identical basic enum with convenience functions. |
| `src/compiler/20.hir/hir_types.spl` | `Effect` struct wrapping `EffectKind` enum: `Pure`, `IO`, `Async`, `Throws(HirType)`, `Mutates`, `Allocates`, `Custom(text)` | Embedded in the HIR type system. Used by `HirTypeKind.Function(params, ret, effects)` and `HirFunction.effects`. |
| `src/compiler/50.mir/mir_effects.spl` | `AsyncEffect`: `Compute`, `Io`, `Wait`; production `Effect`: `Compute`, `Io`, `Wait`, `GcAlloc`, `Net`, `Fs`, `Unsafe` | MIR-level effect tracking with Lean-aligned formal model. Includes `EffectSet`, `BuiltinFunc` mappings. |
| `src/lib/nogc_async_mut/effects.spl` | `Pure`, `Io`, `Net`, `Fs`, `Unsafe`, `Async` | Library-level effect annotations via decorators. |

#### Effect Scanning and Solving

| File | Purpose | Status |
|------|---------|--------|
| `src/compiler/00.common/effects_scanner.spl` | Scans simplified `HirExpr` (local placeholder enum, not real HIR) for suspension operators. Detects `~`, `~=`, `if~`, `while~`, `for~`. | Complete but uses placeholder types, not integrated with real HIR. |
| `src/compiler/00.common/effects_solver.spl` | Fixed-point solver that iteratively infers effects until convergence. Uses simplified `HirFunction`/`HirExpr` placeholders. | Complete with tests, but not connected to the real compiler pipeline. |
| `src/compiler/00.common/effects_env.spl` | `EffectEnv` class tracking function-to-effect mappings with dirty tracking for fixed-point iteration. | Complete but standalone. |
| `src/compiler/00.common/effects_cache.spl` | `EffectCache` for incremental compilation -- caches `FunctionEffectInfo` results. | Complete, clean interface, not wired in. |
| `src/compiler/00.common/effects_promises.spl` | `TypeWrapper` for wrapping/unwrapping `Promise<T>` based on effects. Uses local placeholder `HirType`. | Complete but uses its own simplified type system, not real HIR types. |

#### Type Inference Integration

| File | Purpose | Status |
|------|---------|--------|
| `src/compiler/30.types/type_system/effects.spl` | Full effect inference system with `FunctionInfo`, SCC-based propagation via Tarjan's algorithm, validation, promise wrapping, await inference, `TypedAwaitMode`. | Complete algorithmic implementation. Uses `Dict<text, Effect>` for environment (not real symbol table). |
| `src/compiler/30.types/type_infer/inference_effects.spl` | `HmInferContext` impl methods: `infer_expr_effects`, `check_effect_compatibility`, `merge_effects`, `get_function_effects`. Operates on real `HirExpr`/`HirType`. | Partially integrated -- methods exist on the context but are never called from the main inference path. |
| `src/compiler/30.types/type_infer/inference_expr.spl` | Main expression inference. `HirTypeKind.Function` carries `effects: [Effect]` but effects are always `[]` -- never populated during inference. | Effects field exists structurally but is unused. |

#### HIR/Frontend Integration

| File | Purpose | Status |
|------|---------|--------|
| `src/compiler/20.hir/hir_definitions.spl` | `HirFunction` has `effects: [Effect]` and `is_async: bool` fields. | Fields exist, `effects` always populated as `[]` during lowering (line 248 of `items.spl`). |
| `src/compiler/20.hir/hir_lowering/async.spl` | Validates async functions: checks `Future<T>` return type, poll function signatures, state enum structure. | Complete validation infrastructure, wired into HIR lowering. |
| `src/compiler/10.frontend/desugar/suspension_analysis.spl` | Finds suspension points (`await` expressions) in async function bodies for state machine generation. | Complete, operational. |
| `src/compiler/10.frontend/parser_types.spl` | `Function.is_async` boolean parsed from `async fn` syntax. | Working -- parser sets it via `parse_fn_decl(is_async=1)`. |
| `src/compiler/90.tools/async_integration.spl` | MIR-to-runtime bridge for async state machines. Analyzes MIR bodies for await/yield/receive. | Partial implementation, some stubs. |

#### Formal Verification

| File | Purpose |
|------|---------|
| `verification/type_inference_compile/src/AsyncEffectInference.lean` | Lean 4 formal model proving: effect determinism, suspension implies async, sync safety, async propagation, no double-wrap for promises, await inference soundness, effect join algebra. |

### 1.2 What Is Missing

1. **No single canonical Effect type.** The HIR `EffectKind` enum is the richest (`Pure`, `IO`, `Async`, `Throws(HirType)`, `Mutates`, `Allocates`, `Custom(text)`), but the standalone modules in `00.common/` use simpler `Sync`/`Async` enums with placeholder types. There is no unified definition.

2. **Effect inference is not invoked during compilation.** The `CompilerDriver.compile()` method in `driver.spl` does not call any effect inference pass. The pipeline goes: Parse -> Lower to HIR -> Type Check -> Monomorphize -> Codegen, with no effect analysis step.

3. **`HirFunction.effects` is always `[]`.** During HIR lowering (`hir_lowering/items.spl` line 248), effects are hardcoded to an empty list. No pass populates them.

4. **`HirTypeKind.Function(params, ret, effects)` effects are always `[]`.** When the type inference engine constructs function types, effects is always `[]`. There is no mechanism to populate it from inference.

5. **`inference_effects.spl` methods are never called.** The `HmInferContext` has `infer_expr_effects`, `check_effect_compatibility`, and `merge_effects` but no call site invokes them from the main inference path (`infer_expr`, `check_expr`, `synthesize_expr`).

6. **The fixed-point solver operates on placeholder types.** `effects_solver.spl` uses its own `HirExpr`/`HirFunction` enums, not the real compiler types.

7. **No enforcement of sync/async calling discipline.** There is no check that prevents calling an async function from a sync context (or produces a diagnostic if you do).

8. **No automatic Promise wrapping in the type system.** The type checker does not transform return types of async functions to `Promise<T>`.

9. **No await inference in the type checker.** The `TypedAwaitMode` and `shouldInsertAwait` logic exists but is not invoked during expression type inference.

---

## 2. Effect Types

### 2.1 Proposed Unified Effect Set

Based on analysis of all existing definitions, the unified effect type should live in the HIR layer (since it is the canonical intermediate representation used by type checking). The existing `Effect`/`EffectKind` in `hir_types.spl` is the right starting point:

```simple
struct Effect:
    kind: EffectKind
    span: Span

enum EffectKind:
    Pure            # No side effects -- referentially transparent
    IO              # I/O operations (console, file system, network)
    Async           # May suspend execution, returns Promise<T>
    Throws(type_: HirType)  # Can produce error of given type
    Mutates         # Mutates shared state
    Allocates       # Performs heap allocation
    Custom(name: text)       # User-defined effect (future extension)
```

This is **already defined** in `hir_types.spl`. No new enum is needed.

### 2.2 Effect Hierarchy

For checking purposes, effects form a partial order (lattice):

```
           Any (top)
          / | \
       IO  Async  Mutates  Allocates  Throws(E)
         \  |  /
          Pure (bottom)
```

- `Pure` is the most restrictive: no side effects at all.
- `IO` subsumes `Pure` (an IO function can call pure functions).
- `Async` subsumes `Pure` (an async function can call pure functions).
- `Any` permits all effects (default for unannotated functions in the initial phase).

**Key rule (Kotlin model):** A function with `Async` effect can call functions with `Pure`, `IO`, `Mutates`, or `Allocates` effects. A function with only `Pure` effect cannot call functions with `IO`, `Async`, `Mutates`, or `Allocates` effects.

### 2.3 Initial Scope

For the first integration phase, focus on **only two effects**: `Async` and `Pure`/default (everything else). This matches the Lean 4 model and the existing `Sync`/`Async` infrastructure. The richer effect kinds (`IO`, `Mutates`, `Allocates`, `Throws`) can be layered on later without changing the architecture.

---

## 3. Type Integration

### 3.1 Effects on Function Types

The `HirTypeKind.Function` already carries an `effects` field:

```simple
Function(params: [HirType], ret: HirType, effects: [Effect])
```

Currently, `effects` is always `[]`. After integration:

- A function declared as `async fn fetch() -> text` will have:
  ```
  Function(params: [], ret: Str, effects: [Effect(kind: Async, span: ...)])
  ```

- A plain `fn compute(x: i64) -> i64` will have:
  ```
  Function(params: [Int(64, true)], ret: Int(64, true), effects: [])
  ```

The effects list on the type is the **declared** (or inferred) effects of that function. When stored in the type system, effects are part of the function's identity -- two function types with different effects are not unifiable.

### 3.2 Async Return Type Transformation

Following the Lean model (`transformReturnType`), async functions undergo return type wrapping:

```simple
# User writes:
async fn fetch(url: text) -> text:
    val response = ~http_get(url)
    response.body

# Type system sees:
# fn fetch(url: text) -> Promise<text>   [effects: [Async]]
```

**No double-wrap rule (proven in Lean):** If user explicitly returns `Promise<T>`, no wrapping occurs:

```simple
async fn manual_promise() -> Promise<text>:
    Promise.resolve("already wrapped")
# Type: fn() -> Promise<text>   [effects: [Async]]  -- no double wrap
```

### 3.3 Suspension Operator Typing

The `~` prefix operator (and `~=`, `if~`, `while~`, `for~` variants) unwraps `Promise<T>` to `T`:

```simple
# If http_get returns Promise<Response>:
val response: Response = ~http_get(url)
#                        ^ suspension: Promise<Response> -> Response
```

Type rule: `~expr` where `expr: Promise<T>` has type `T`. If `expr` is not `Promise<T>`, this is a type error.

### 3.4 Implicit Await Inference

Following the Lean model (`shouldInsertAwait`), when assigning `Promise<T>` to a variable of type `T`, the compiler inserts an implicit await:

```simple
async fn example():
    val data: text = fetch("url")  # fetch returns Promise<text>
    # Compiler inserts: val data: text = ~fetch("url")
```

This is bidirectional: the expected type `text` and the actual type `Promise<text>` trigger the implicit await.

---

## 4. Inference Rules

### 4.1 Effect Inference Algorithm

The algorithm matches the Lean 4 model and the existing `effects_solver.spl` logic, but operates on real HIR types:

1. **Initialization:** All functions start with `effects = []` (unknown).

2. **Explicit annotation:** If `is_async == true`, add `EffectKind.Async` to effects.

3. **Body scanning:** Walk the function body HIR expression tree:
   - Suspension operator (`~`, `~=`, `if~`, `while~`, `for~`) => `Async`
   - Call to function with `Async` effect => `Async`
   - All other expressions => no new effect

4. **Fixed-point iteration:** For mutually recursive functions, iterate until stable (existing Tarjan SCC algorithm in `effects.spl` handles this correctly).

5. **Validation:** If function is annotated `sync` but body contains suspension or calls async, emit error.

### 4.2 Effect Propagation Rules

These rules are already proven in the Lean verification:

| Expression | Effect |
|-----------|--------|
| Literal (`42`, `"hello"`, `true`) | `[]` (pure) |
| Variable read | `[]` (pure) |
| Binary/unary operation | union of operand effects |
| `~expr` (suspension) | `[Async]` |
| `f(args...)` where `f` has effects `E` | `E` union effects of each `arg` |
| `if cond: then else: else_` | union of all branch effects |
| `match` expression | union of scrutinee and all arm effects |
| `for x in iter: body` | union of `iter` effects and `body` effects |
| `while cond: body` | union of `cond` effects and `body` effects |
| Block `{ stmts; expr }` | union of all statement effects and final expression effects |
| Lambda `\x: body` | effects of `body` (captured into the lambda's function type) |

### 4.3 Bidirectional Integration

Effect checking integrates with the existing bidirectional type checking framework in `inference_expr.spl`:

- **Synthesize mode:** When synthesizing the type of a function call, also synthesize the effects by looking up the callee's function type and extracting its effects.

- **Check mode:** When checking an expression against an expected type, also check effect compatibility. If the expected context is `Pure`, reject expressions with `Async` or `IO` effects.

---

## 5. Checking Rules

### 5.1 Sync-Cannot-Call-Async

The primary enforcement rule. A function without the `Async` effect cannot call a function with the `Async` effect, unless the call is wrapped in a coroutine builder:

```simple
fn process() -> text:
    val data = fetch("url")  # ERROR: calling async from sync context
    data

async fn process_async() -> text:
    val data = ~fetch("url")  # OK: async context
    data
```

**Error message:**
```
error[E0401]: cannot call async function `fetch` from sync context
  --> src/example.spl:2:16
   |
2  |     val data = fetch("url")
   |                ^^^^^^^^^^^^
   |
   = help: mark this function as `async fn process()` or use `spawn { fetch("url") }`
```

### 5.2 Suspension-Only-In-Async

The `~` operator can only appear inside functions with `Async` effect:

```simple
fn bad() -> text:
    val x = ~some_promise   # ERROR: suspension in sync function
    x
```

This is already handled by `validate_sync_constraint` in the Lean model and `validate_suspension_context` in `effects.spl`.

### 5.3 Promise Type Mismatch

If `~` is applied to a non-Promise type, that is a type error:

```simple
async fn example():
    val x = ~42   # ERROR: ~ applied to i64, expected Promise<T>
```

### 5.4 Effect Compatibility for Higher-Order Functions

When passing a function as an argument, the callee's expected effect must be compatible:

```simple
fn map_sync(f: fn(i64) -> i64, items: [i64]) -> [i64]:
    # f is expected to be sync (no Async effect)
    ...

async fn double_async(x: i64) -> i64:
    ~sleep(100)
    x * 2

fn bad():
    map_sync(double_async, [1, 2, 3])  # ERROR: passing async fn where sync fn expected
```

### 5.5 Gradual Enforcement

In the initial phase, effect violations should be **warnings**, not errors, to avoid breaking existing code. This can be controlled via a compiler flag:

```simple
# Strict mode (errors):
bin/simple build --strict-effects

# Default mode (warnings):
bin/simple build   # effect violations are warnings
```

---

## 6. Integration Points

### 6.1 Pipeline Placement

The effect inference pass should be inserted into the compilation pipeline between HIR lowering and type checking. Here is the current pipeline with the proposed insertion point:

```
Phase 1: Load sources
Phase 2: Parse all sources
Phase 3: Lower to HIR + resolve + type check
  3a: Lower AST to HIR           (existing)
  3b: Method resolution           (existing)
  3c: [NEW] Effect inference      <-- Insert here
  3d: Type checking               (existing, enhanced)
Phase 4: Monomorphization
Phase 5: Mode-specific (interpret/compile/check)
```

Effect inference in Phase 3c:
1. Collect all `HirFunction` definitions from HIR modules
2. Build `FunctionInfo` structs from real HIR data
3. Run SCC-based propagation (`propagate_effects_transitive`)
4. Write inferred effects back to `HirFunction.effects`
5. Populate effects on `HirTypeKind.Function` wherever function types appear

### 6.2 File-Level Changes

| File | Change |
|------|--------|
| `src/compiler/80.driver/driver.spl` | Add call to effect inference pass between HIR lowering and type checking in `lower_and_check_impl`. |
| `src/compiler/20.hir/hir_lowering/items.spl` | Replace `effects: []` with effects inferred from `is_async` annotation (initial seed before full inference). |
| `src/compiler/30.types/type_infer/inference_expr.spl` | In `infer_expr` for `Call` and `MethodCall`, propagate callee effects. In lambda/closure inference, capture body effects into function type. |
| `src/compiler/30.types/type_infer/inference_effects.spl` | Wire `check_effect_compatibility` into the main type checking path. Add call from `infer_expr` when checking function calls. |
| `src/compiler/30.types/type_system/effects.spl` | Adapt `FunctionInfo` to use real `SymbolId` instead of `text` for function names. Connect to HIR symbol table. |
| `src/compiler/30.types/type_infer_types.spl` | No change needed (uses `HirType` which already has effects). |

### 6.3 New Module: Effect Pass Coordinator

A new file `src/compiler/30.types/type_system/effect_pass.spl` should coordinate the full effect inference pass:

```simple
# Effect Pass - Coordinator for effect inference

fn run_effect_pass(modules: Dict<text, HirModule>) -> Result<(), [EffectError]>:
    """Run effect inference across all modules.

    1. Collect function info from all modules
    2. Build effect environment with builtins
    3. Run SCC-based propagation
    4. Write effects back to HIR functions
    5. Validate constraints
    """
    # Step 1: Collect
    var functions: [FunctionInfo] = []
    for (name, module) in modules:
        for (sym_id, func) in module.functions:
            functions = functions.push(build_function_info(func, module))

    # Step 2: Propagate
    val env = propagate_effects_transitive(functions)

    # Step 3: Write back
    for (name, module) in modules:
        write_effects_to_module(module, env)

    # Step 4: Validate
    var errors: [EffectError] = []
    for func_info in functions:
        val validation = validate_sync_constraint(func_info)
        if validation.is_err():
            errors = errors.push(validation.unwrap_err())

    if errors.is_empty():
        Ok(())
    else:
        Err(errors)
```

### 6.4 Type Checker Integration Points

Within `HmInferContext.infer_expr` (the main inference dispatch), these specific cases need enhancement:

**Function Call (`Call` case, line ~306 of `inference_expr.spl`):**

After inferring the callee type and unifying argument types, extract the callee's effects from its function type and:
1. Record the effects in the current function's accumulated effect set
2. If the current function is sync and the callee has `Async`, emit a diagnostic

**Closure/Lambda (`Closure` case, line ~478):**

After inferring the body type, also infer the body's effects and include them in the constructed `HirTypeKind.Function`:

```simple
# Current (line 497):
Ok(HirType(
    kind: HirTypeKind.Function(resolved_params, self.resolve(body_ty), []),
    span: span
))

# After integration:
val body_effects = self.infer_expr_effects(body)
Ok(HirType(
    kind: HirTypeKind.Function(resolved_params, self.resolve(body_ty), body_effects),
    span: span
))
```

**Bidirectional Check (`check_expr` for Closure, line ~62):**

When checking a closure against an expected function type, also check that the body's effects are compatible with the expected effects.

---

## 7. Implementation Plan

### Phase 1: Unify Effect Types (Low Risk, 1-2 Days)

**Goal:** Establish a single canonical Effect definition.

- Remove duplicate `Effect` enums from `00.common/effects.spl`, `effects_v1_simple.spl`, `effects_solver.spl`, `effects_scanner.spl`, `effects_promises.spl`, `effects_env.spl`.
- All modules should import `Effect`/`EffectKind` from `hir_types.spl`.
- Adapt the `EffectEnv`, `EffectScanner`, `EffectSolver` to use `SymbolId` (or at minimum `text` function names that match HIR) instead of their local placeholder types.
- Keep existing tests passing by updating imports.

### Phase 2: Wire Effect Inference into the Pipeline (Medium Risk, 2-3 Days)

**Goal:** Effects are actually inferred and stored on `HirFunction`.

- Create `src/compiler/30.types/type_system/effect_pass.spl` as the coordinator.
- In `driver.spl`, call `run_effect_pass` after HIR lowering but before type checking.
- Build `FunctionInfo` from real `HirFunction` data (name, `is_async`, body walk for suspension, called functions from HIR expression tree).
- Write inferred effects back to `HirFunction.effects`.
- Add `EffectKind.Async` to `effects` when `is_async == true` (initial seed).
- Add basic logging/stats output.

### Phase 3: Populate Effects on Function Types (Medium Risk, 2-3 Days)

**Goal:** `HirTypeKind.Function.effects` is populated during type inference.

- In `inference_expr.spl`, when constructing function types for closures, populate effects from body analysis.
- When looking up a function symbol and constructing its type, copy effects from the `HirFunction` definition.
- Ensure effects survive unification (effects are structural, not unified -- two function types with different effects should not unify).

### Phase 4: Async-from-Sync Checking (Low Risk, 1-2 Days)

**Goal:** Emit warnings when calling async from sync.

- In `inference_expr.spl` `Call` case, after resolving callee type, check if callee has `Async` effect and current context does not.
- Track "current function effect context" in `HmInferContext` (add a field for the enclosing function's effects).
- Emit warning (not error) for violations.
- Add `--strict-effects` flag to upgrade warnings to errors.

### Phase 5: Promise Wrapping and Await Inference (Medium Risk, 2-3 Days)

**Goal:** The type system automatically wraps async return types in `Promise<T>` and infers `~` (await) at suspension points.

- During type inference for function call expressions, if the callee is async and the result type is used where `T` (not `Promise<T>`) is expected, insert implicit await and emit the inner type.
- In bidirectional check mode, when expected type is `T` and synthesized type is `Promise<T>`, succeed (implicit await).
- Validate that `~` is applied only to `Promise<T>` types.
- Use the no-double-wrap rule from the Lean model.

### Phase 6: Full Effect Propagation (Lower Priority, 3-5 Days)

**Goal:** Track `IO`, `Mutates`, `Allocates`, and `Throws` effects.

- Extend body scanning to detect IO operations (print, file read, etc.), mutations (`me` method calls, assignment to shared state), allocations.
- Populate `Throws(HirType)` from `?` operator usage and function signatures.
- Support `@pure` annotation that enforces no effects.
- Support AOP effect predicates (`Effect(text)` selector in `predicate.spl`).

### Phase 7: Incremental and Cache Integration (Lower Priority, 1-2 Days)

**Goal:** Effect inference results are cached for incremental compilation.

- Wire `EffectCache` from `effects_cache.spl` into the effect pass.
- Store `FunctionEffectInfo` per function.
- On incremental recompilation, skip effect analysis for unchanged functions.
- Invalidate dependent functions when a function's effect changes.

---

## Appendix A: Existing Test Coverage

The following test files exercise effect infrastructure (all use standalone placeholder types, not integrated):

| File | Tests |
|------|-------|
| `src/compiler/00.common/effects.spl` | `test_effect_basic`, `test_effect_combine`, `test_effect_combine_all`, `test_effect_env_basic`, `test_effect_env_set_get`, `test_effect_env_dirty`, `test_builtins` |
| `src/compiler/00.common/effects_solver.spl` | `test_single_function`, `test_async_function`, `test_call_chain`, `test_mixed_functions`, `test_convergence` |
| `src/compiler/00.common/effects_scanner.spl` | `test_literals`, `test_suspend_operators`, `test_function_calls`, `test_control_flow`, `test_nested` |
| `src/compiler/00.common/effects_promises.spl` | `test_basic_types`, `test_promise_wrap`, `test_promise_unwrap`, `test_suspend_validation`, `test_nested_promises`, `test_function_types` |
| `verification/type_inference_compile/src/AsyncEffectInference.lean` | 13 formal theorems: determinism, suspension_implies_async, sync_safety, async_propagation, no_double_wrap, await_inference_sound, promise_unwrap_correct, effect_join algebra (commutative, idempotent, absorbing, identity) |

## Appendix B: Key File Paths

All paths are relative to the project root (`/home/ormastes/dev/pub/simple/`):

```
# HIR type definitions (canonical Effect/EffectKind)
src/compiler/20.hir/hir_types.spl

# HIR function definitions (HirFunction with effects field)
src/compiler/20.hir/hir_definitions.spl

# HIR lowering (where effects: [] is hardcoded)
src/compiler/20.hir/hir_lowering/items.spl

# Main type checker
src/compiler/30.types/type_system/checker.spl

# Expression inference (main entry point for type inference)
src/compiler/30.types/type_infer/inference_expr.spl

# Effect inference methods on HmInferContext
src/compiler/30.types/type_infer/inference_effects.spl

# Control flow + effect inference coordinator
src/compiler/30.types/type_infer/inference_control.spl

# Standalone effect infrastructure (to be unified)
src/compiler/00.common/effects.spl
src/compiler/00.common/effects_solver.spl
src/compiler/00.common/effects_scanner.spl
src/compiler/00.common/effects_env.spl
src/compiler/00.common/effects_cache.spl
src/compiler/00.common/effects_promises.spl
src/compiler/00.common/effects_v1_simple.spl

# SCC-based effect propagation + Tarjan's algorithm
src/compiler/30.types/type_system/effects.spl

# MIR effect tracking
src/compiler/50.mir/mir_effects.spl

# Async HIR lowering (Future<T> validation)
src/compiler/20.hir/hir_lowering/async.spl

# Frontend desugar (suspension analysis, state machine)
src/compiler/10.frontend/desugar/suspension_analysis.spl
src/compiler/10.frontend/desugar/mod.spl

# Async runtime integration (MIR -> state machine)
src/compiler/90.tools/async_integration.spl

# Library-level effect decorators
src/lib/nogc_async_mut/effects.spl

# Compiler driver (pipeline orchestration)
src/compiler/80.driver/driver.spl

# Formal verification
verification/type_inference_compile/src/AsyncEffectInference.lean
```

## Appendix C: Simple Language Syntax Examples

### Async Function Declaration

```simple
async fn fetch_user(id: i64) -> User:
    val response = ~http_get("/users/{id}")
    parse_user(response.body)
```

### Suspension Operators

```simple
# Explicit suspension (await)
val result = ~async_operation()

# Suspend-assign
result ~= async_operation()

# Suspend in control flow
if~ condition_future():
    handle_true()

while~ poll_status():
    process_item()

for~ item in async_stream():
    handle(item)
```

### Effect Annotations (Future Extension)

```simple
@pure
fn add(x: i64, y: i64) -> i64:
    x + y

@io
fn greet(name: text):
    print("Hello, {name}!")

async fn fetch(url: text) -> text:
    val response = ~http_get(url)
    response.body
```

### Spawn for Async-from-Sync

```simple
fn main():
    # Cannot directly call async from sync
    # val data = fetch("url")  # ERROR

    # Use spawn to create a concurrent task
    val task = spawn:
        fetch("url")
    val data = task.join()
```
