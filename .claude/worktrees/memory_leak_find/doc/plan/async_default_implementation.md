# Async Default Implementation Plan

**Status:** Planning
**Target:** Simple Language v0.2
**Last Updated:** 2026-01-05

## Overview

Implement async-by-default function semantics where `fn` can suspend and `sync fn` is explicitly non-suspending.

## Features to Implement

| Feature | ID | Difficulty | Dependencies |
|---------|-----|------------|--------------|
| Async Default | #44 | 3 | #41 (Async/Await) |
| Suspension Operator (~) | #45 | 3 | #44 |
| Effect Inference | #46 | 4 | #44, #45 |
| Promise Type | #47 | 3 | #44 |

## Current State

### Completed
- ✅ Basic async/await (#41) - Runtime support exists
- ✅ Futures (#43) - RuntimeFuture implemented
- ✅ Generators (#42) - RuntimeGenerator implemented
- ✅ Lean verification model - AsyncEffectInference.lean generated

### Missing
- ❌ Parser support for `sync fn` keyword
- ❌ Effect inference in type checker
- ❌ Promise type in standard library
- ❌ Suspension operators (~=, if~, while~, for~)
- ❌ Implicit Promise wrapping for async functions
- ❌ Type-driven await inference

## Implementation Phases

### Phase 1: Foundation (Week 1)

**Goal:** Add parser and AST support

1. **Parser: Add `sync` keyword**
   - File: `src/parser/src/parser.rs`
   - Add `sync` to function modifiers
   - Update AST to track sync/async

2. **AST: Function modifiers**
   - File: `src/parser/src/ast.rs`
   - Add `is_sync: bool` to `FunctionDef`
   - Update all AST construction

3. **Tests**
   - File: `src/parser/tests/parser_tests.rs`
   - Test `sync fn foo()` parsing
   - Test `fn foo()` defaults to async

### Phase 2: Effect System (Week 2)

**Goal:** Implement effect inference

1. **Type Checker: Effect tracking**
   - File: `src/type/src/lib.rs` (new `effects.rs` module)
   - Add `Effect` enum (Sync, Async)
   - Implement effect inference algorithm
   - Track function effects in type environment

2. **MIR: Effect annotations**
   - File: `src/compiler/src/mir/types.rs`
   - Add effect metadata to MIR functions
   - Validate sync functions don't suspend

3. **Tests**
   - File: `src/type/tests/effect_tests.rs` (new)
   - Test effect inference from function body
   - Test sync constraint validation
   - Test mutual recursion handling

### Phase 3: Promise Type (Week 3)

**Goal:** Implement Promise[T] in standard library

1. **Promise class**
   - File: `simple/std_lib/src/compiler_core/promise.spl` (new)
   - Implement Promise[T] class
   - Add resolve/reject/then/catch methods
   - Implement Promise.all/race/any/allSettled

2. **Runtime support**
   - File: `src/runtime/src/value/async_gen.rs`
   - Extend RuntimeFuture to support Promise API
   - Add Promise-related FFI functions

3. **Tests**
   - File: `simple/std_lib/test/unit/compiler_core/promise_spec.spl`
   - Test Promise creation and chaining
   - Test combinator methods
   - Test error handling

### Phase 4: Suspension Operators (Week 4)

**Goal:** Implement ~=, if~, while~, for~ operators

1. **Lexer: Add suspension operators**
   - File: `src/parser/src/lexer.rs`
   - Add `~=` token (TildeEquals)
   - Add `if~` token (IfTilde)
   - Add `while~` token (WhileTilde)
   - Add `for~` token (ForTilde)

2. **Parser: Suspension syntax**
   - File: `src/parser/src/statements/mod.rs`
   - Parse `x ~= expr` as AwaitAssign
   - Parse `if~ cond:` as AwaitIf
   - Parse `while~ cond:` as AwaitWhile
   - Parse `for~ x in iter:` as AwaitFor

3. **AST: Suspension nodes**
   - File: `src/parser/src/ast.rs`
   - Add AwaitAssign statement
   - Add suspension flags to If/While/For

4. **MIR: Lower suspension**
   - File: `src/compiler/src/mir/lower.rs`
   - Lower AwaitAssign to Await instruction
   - Lower suspension control flow properly

5. **Tests**
   - File: `src/parser/tests/suspension_tests.rs` (new)
   - Test all suspension operators parse correctly
   - Test lowering to MIR

### Phase 5: Implicit Promise Wrapping (Week 5)

**Goal:** Async functions implicitly return Promise[T]

1. **Type Inference: Promise wrapping**
   - File: `src/type/src/lib.rs`
   - Wrap async function return types in Promise[T]
   - Handle explicit Promise[T] returns (no double-wrap)

2. **MIR: Return type adjustment**
   - File: `src/compiler/src/mir/lower.rs`
   - Adjust function signatures for async functions
   - Wrap return values in Promise

3. **Codegen: Promise allocation**
   - File: `src/compiler/src/codegen/cranelift.rs`
   - Allocate Promise on async function entry
   - Resolve/reject Promise on return/error

4. **Tests**
   - File: `src/type/tests/promise_wrap_tests.rs` (new)
   - Test Promise wrapping inference
   - Test explicit Promise return no double-wrap
   - Test Promise unwrapping with ~=

### Phase 6: Type-Driven Await (Week 6)

**Goal:** Infer await from type mismatch

1. **Type Checker: Await inference**
   - File: `src/type/src/lib.rs`
   - Detect Promise[T] → T assignment
   - Insert implicit await
   - Update type unification

2. **MIR: Implicit await**
   - File: `src/compiler/src/mir/lower.rs`
   - Generate Await instructions for inferred awaits

3. **Tests**
   - File: `src/type/tests/await_inference_tests.rs` (new)
   - Test `let x: T = async_fn()` inserts await
   - Test `let p: Promise[T] = async_fn()` doesn't await

### Phase 7: Integration & Testing (Week 7)

**Goal:** End-to-end testing and documentation

1. **Integration tests**
   - File: `src/driver/tests/async_default_tests.rs` (new)
   - Test full async-default workflow
   - Test sync constraint enforcement
   - Test Promise chaining

2. **Simple tests**
   - Files: `simple/std_lib/test/features/concurrency/*_spec.spl`
   - Enable all 4 skipped specs (#44-#47)
   - Run and verify 50+ tests pass

3. **Documentation**
   - Update `doc/spec/async_default.md` with implementation notes
   - Update `doc/features/concurrency/004*_*.md` with examples
   - Add migration guide

## Technical Design

### Effect Inference Algorithm

```rust
fn infer_effect(fn_body: &Block, env: &TypeEnv) -> Effect {
    // Check for explicit suspension operators
    if has_suspension_operator(fn_body) {
        return Effect::Async;
    }

    // Check function calls
    for call in fn_body.calls() {
        match env.get_effect(call.name) {
            Some(Effect::Async) => return Effect::Async,
            Some(Effect::Sync) => continue,
            None => {
                // Mutual recursion: defer to fixed-point iteration
                deferred.push(call);
            }
        }
    }

    // Handle deferred cases with fixed-point
    if !deferred.is_empty() {
        return fixed_point_inference(fn_body, env);
    }

    Effect::Sync
}

fn fixed_point_inference(fns: &[Function], env: &mut TypeEnv) {
    loop {
        let mut changed = false;
        for fn in fns {
            let old_effect = env.get_effect(fn.name);
            let new_effect = infer_effect(&fn.body, env);
            if old_effect != Some(new_effect) {
                env.set_effect(fn.name, new_effect);
                changed = true;
            }
        }
        if !changed { break; }
    }
}
```

### Promise Type Implementation

```simple
# File: simple/std_lib/src/compiler_core/promise.spl

enum PromiseState:
    Pending
    Fulfilled(value: Any)
    Rejected(error: Error)

class Promise[T]:
    _state: PromiseState
    _then_callbacks: List[fn(T) -> Any]
    _catch_callbacks: List[fn(Error) -> T]

    @static
    fn new(executor: fn(resolve: fn(T), reject: fn(Error))) -> Promise[T]:
        let promise = Promise[T](_state: PromiseState.Pending, _then_callbacks: [], _catch_callbacks: [])
        executor(
            resolve: \value: promise._resolve(value),
            reject: \error: promise._reject(error)
        )
        return promise

    @static
    fn resolve(value: T) -> Promise[T]:
        let promise = Promise[T](_state: PromiseState.Fulfilled(value), _then_callbacks: [], _catch_callbacks: [])
        return promise

    @static
    fn reject(error: Error) -> Promise[T]:
        let promise = Promise[T](_state: PromiseState.Rejected(error), _then_callbacks: [], _catch_callbacks: [])
        return promise

    fn then[U](mut self, on_fulfilled: fn(T) -> U) -> Promise[U]:
        match self._state:
            case Fulfilled(value):
                return Promise.resolve(on_fulfilled(value))
            case Rejected(error):
                return Promise.reject(error)
            case Pending:
                # Chain callback
                self._then_callbacks.append(on_fulfilled)
                return self  # Simplified - would need new promise

    fn catch(mut self, on_rejected: fn(Error) -> T) -> Promise[T]:
        match self._state:
            case Rejected(error):
                return Promise.resolve(on_rejected(error))
            case Fulfilled(value):
                return Promise.resolve(value)
            case Pending:
                self._catch_callbacks.append(on_rejected)
                return self

    @static
    fn all(promises: List[Promise[T]]) -> Promise[List[T]]:
        # Wait for all promises to fulfill
        # Implementation uses runtime support
        ...

    @static
    fn race(promises: List[Promise[T]]) -> Promise[T]:
        # Return first promise to settle
        ...

    @static
    fn any(promises: List[Promise[T]]) -> Promise[T]:
        # Return first promise to fulfill
        ...
```

## Migration Strategy

### Stage 1: Parser Support (Non-Breaking)
- Add `sync fn` syntax
- All `fn` continue to work as before
- Optional lint: warn on functions that could be `sync`

### Stage 2: Effect Inference (Non-Breaking)
- Infer effects but don't change behavior
- Add `--effect-check` flag to validate sync constraints
- Report effect mismatches as warnings

### Stage 3: Promise Wrapping (Breaking)
- Async functions now return Promise[T]
- Add migration tool to update call sites
- Provide compat mode for gradual migration

### Stage 4: Suspension Operators (Additive)
- Add ~=, if~, while~, for~ operators
- Existing `await` still works
- Gradually migrate codebase to use ~=

## Success Criteria

- [ ] All 4 features (#44-#47) marked ✅ Complete in feature.md
- [ ] 50+ BDD tests pass in `simple/std_lib/test/features/concurrency/`
- [ ] Lean verification model matches implementation
- [ ] Documentation complete with examples
- [ ] Migration guide written and tested
- [ ] Performance: async overhead < 10% vs sync baseline

## Timeline

| Phase | Week | Deliverable |
|-------|------|-------------|
| 1 | Jan 6-12 | Parser & AST for `sync fn` |
| 2 | Jan 13-19 | Effect inference algorithm |
| 3 | Jan 20-26 | Promise[T] standard library |
| 4 | Jan 27-Feb 2 | Suspension operators |
| 5 | Feb 3-9 | Implicit Promise wrapping |
| 6 | Feb 10-16 | Type-driven await |
| 7 | Feb 17-23 | Integration & testing |

**Target Completion:** February 23, 2026

## Risk Mitigation

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Effect inference too slow | Medium | High | Use caching, incremental analysis |
| Promise overhead too high | Medium | High | Pool allocations, optimize hot path |
| Migration breaks existing code | High | Medium | Provide compat mode, migration tool |
| Suspension operators confusing | Low | Medium | Good documentation, examples |

## References

- [Async Default Spec](../spec/async_default.md)
- [Suspension Operator Spec](../spec/suspension_operator.md)
- [AsyncEffectInference.lean](../../verification/type_inference_compile/src/AsyncEffectInference.lean)
- [Python async/await](https://peps.python.org/pep-0492/)
- [JavaScript Promises](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Promise)
- [Rust async book](https://rust-lang.github.io/async-book/)
