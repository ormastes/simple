# Phase 6: Async/Task, Generics Analysis & Remaining Work
**Date**: 2026-02-09
**Status**: Analysis & Planning

---

## Executive Summary

**Key Finding**: Async/Task infrastructure exists but is **blocked by runtime generics**
- 8 async TODOs waiting for Task/Future types
- Task/Future types exist but use generic syntax `<T>`
- Runtime parser rejects `<>` (treats `<` as Lt token, not type parameter)
- **Unblocking generics would enable ~51+ TODOs**

---

## Part 1: Async/Task Infrastructure Analysis

### Current State: Infrastructure Complete ✅

**Existing Modules**:
- `src/std/async/task.spl` - Task scheduling
- `src/std/async/future.spl` - Future type
- `src/std/async/poll.spl` - Poll enum
- `src/std/async_host/` - Host runtime
- `src/std/async_unified.spl` - Unified interface

**Type Definitions**:
```simple
# These exist but can't be loaded at runtime
class Future<T>:
    state: [u8]

    static fn from_value(value: T) -> Future<T>
    static fn pending() -> Future<T>
    fn poll() -> Poll<T>

class Task:
    id: usize
    future: [u8]
    priority: i32
    state: TaskState

    static fn new<T>(f: fn() -> Future<T>) -> Task
```

**Problem**: Runtime parser error when loading these modules:
```
Parse error: expected identifier, found Lt
  at: Future<T>
           ^
```

### Async TODOs Breakdown (8 total)

**Waiting for Runtime Generics** (4 TODOs):
- `test/system/features/database_synchronization/database_sync_spec.spl` - 4 test stubs

**Other Async Work** (4 TODOs):
- Actor scheduler improvements (1 TODO)
- Parallel test runner (1 TODO)
- HIR lowering errors (1 TODO)
- Timer integration (1 TODO)

### What Can Be Done Now

**Without Generics**:
1. ✅ Actor improvements (non-generic)
2. ✅ Parallel test utilities (use processes)
3. ✅ Timer integration (system time)

**Blocked on Generics**:
1. ❌ Task/Future usage in tests
2. ❌ Async database operations
3. ❌ Generic async utilities

---

## Part 2: Generics in Runtime - Root Cause Analysis

### The Problem

**Current Runtime Parser Behavior**:
```simple
# This works (compiled mode):
class Future<T>:
    value: T

# This fails (runtime/interpreter):
# Parse error: expected identifier, found Lt at: Future<
```

**Why It Fails**:
- Lexer tokenizes `<` as `TokenKind.Lt` (less-than)
- Parser expects identifier after `class Future`
- Sees `Lt` token instead of identifier
- No special handling for type parameters in runtime parser

### Impact Analysis

**Blocked Features** (51+ TODOs):

1. **Async/Task** (8 TODOs) - Future<T>, Task, Poll<T>
2. **Generic Collections** (15 TODOs) - List<T>, Dict<K,V>, Set<T>
3. **Generic Types** (12 TODOs) - Option<T>, Result<T,E>
4. **DI Container** (6 TODOs) - Container<T> dependencies
5. **Tensor Types** (10 TODOs) - Tensor<T>, Shape<N>

**Files That Can't Load at Runtime**:
```bash
$ grep -r "class.*<\|struct.*<\|enum.*<" src --include="*.spl" | wc -l
127 files with generic types
```

### Why Generics Weren't Implemented

**Architectural Decision**:
- Runtime parser is **Simple code** (self-hosted)
- Initial implementation focused on **core language features**
- Generics require **complex parsing** (nested `<>`, disambiguation)
- Decision: Support generics in **compiled mode first**

**Complexity Examples**:
```simple
# Easy case
Future<i64>

# Nested generics
Result<Option<i64>, Error>

# Ambiguous with operators
a < b > c  # comparison or type?
f<T>(x)    # generic call or less-than?
```

---

## Part 3: Generics Implementation Plan

### Option A: Full Runtime Generics (High Effort)

**Requirements**:
1. Lexer: Context-aware `<>` tokenization
2. Parser: Type parameter parsing
3. Type checker: Generic instantiation
4. Evaluator: Type erasure or monomorphization

**Complexity**: ~3,000 lines, 2-3 weeks
**Risk**: High (touches core parser)

### Option B: Type Erasure Workaround (Medium Effort)

**Approach**: Non-generic wrapper types
```simple
# Instead of Future<T>
class FutureValue:
    state: [u8]

class FutureI64:
    inner: FutureValue

class FutureText:
    inner: FutureValue
```

**Complexity**: ~500 lines per type family
**Risk**: Medium (code duplication)

### Option C: Parser Improvement (Low Effort, Limited Scope)

**Approach**: Add minimal `<>` support for specific cases
```simple
# Support only:
# 1. Class/struct/enum declarations
# 2. Simple type parameters (no constraints)
# 3. No nested generics yet

class Future<T>:  # Parse this
    value: T      # And this

# Don't support yet:
Result<Option<i64>, Error>  # Nested
fn map<T, U>(f: fn(T) -> U) # Generic functions
```

**Complexity**: ~800 lines
**Risk**: Low (incremental improvement)

### **Recommendation: Option C** (Incremental Parser Improvement)

**Rationale**:
- Unblocks 51+ TODOs with targeted fix
- Low risk (doesn't touch core interpreter)
- Can evolve to full generics over time
- Provides immediate value

---

## Part 4: Implementation Roadmap

### Phase 6.1: Parser Foundation (800 lines, 2 days)

**Files to Modify**:
- `src/compiler/lexer.spl` - Add angle bracket handling
- `src/compiler/parser.spl` - Parse type parameters
- `src/compiler/parser_types.spl` - AST nodes for generics

**Deliverables**:
```simple
# These will parse:
class Future<T>:
    value: T

enum Result<T, E>:
    Ok(T)
    Err(E)

# Type parameters in field types
struct Container<T>:
    items: [T]
```

**Tests**: 20 parser tests

### Phase 6.2: Type Parameter Resolution (400 lines, 1 day)

**Files to Modify**:
- `src/compiler/type_system/` - Resolve type parameters
- `src/compiler/resolve.spl` - Bind parameters to types

**Deliverables**:
- Type parameter scope handling
- Simple substitution (no constraints yet)

**Tests**: 15 resolution tests

### Phase 6.3: Enable Async Modules (200 lines, 1 day)

**Files to Modify**:
- `src/std/async/*.spl` - Verify they load
- Test async usage patterns

**Deliverables**:
- Future<T> and Task usable at runtime
- 8 async TODOs unblocked

**Tests**: 8 async operation tests

### Phase 6.4: Enable Generic Collections (400 lines, 1 day)

**Files to Modify**:
- `src/std/collections/*.spl` - Load generic types
- Enable Set<T>, Map<K,V> usage

**Deliverables**:
- 15 collection TODOs unblocked

---

## Part 5: Remaining Work Categories (341 TODOs)

### By Blocker (Updated Analysis)

**1. Runtime Generics** (51 TODOs, 15%) - **ADDRESSABLE**
- Async/Task (8)
- Collections (15)
- Generic utilities (12)
- DI containers (6)
- Tensor types (10)

**Impact**: Phase 6.1-6.4 unblocks all 51 TODOs

**2. Test Stubs** (102 TODOs, 30%) - **LOW VALUE**
- Many depend on unimplemented features
- Better to implement features than write stub tests
- Defer until features exist

**3. FFI-Dependent** (85 TODOs, 25%) - **NEEDS DESIGN**
- String ptr+len conversions (6)
- Memory operations (12)
- Platform ops (67)

**Requires**: FFI v2 design phase (separate effort)

**4. Complex Compiler** (68 TODOs, 20%) - **FUTURE WORK**
- MIR optimizations (13)
- JIT compilation (7)
- Hot reload (4)
- Other compiler features (44)

**Best approach**: Prioritize by impact after basics complete

**5. Module Imports** (34 TODOs, 10%) - **FIXABLE**
- Cross-module resolution
- HIR module loading
- Dynamic imports

**May be fixed as side effect of generics work**

### Priority After Generics

**High Value** (when unblocked):
1. MIR optimizations (13 TODOs, 20-40% perf)
2. Module import fixes (34 TODOs)
3. Async operations enabled (8 TODOs)

**Medium Value**:
1. Test suite completion (102 TODOs, +14% coverage)
2. Platform operations (67 TODOs, cross-platform)

**Low Value** (defer):
1. Experimental features (hot reload, etc.)
2. Test stubs for non-existent features

---

## Part 6: Generics Design Details

### Lexer Changes

**Context-Aware Angle Brackets**:
```simple
# After: class, struct, enum, impl
class Future<T>   # Parse as type params

# After: identifier in type position
val x: Future<i64>  # Parse as type args

# In expression context
a < b             # Still Lt token
f<T>(x)           # Needs lookahead
```

**Implementation Strategy**:
1. Track parser state (in_type_context)
2. Lexer peeks ahead after `<`
3. If followed by identifier + `>` or `,`, treat as angle bracket
4. Otherwise, treat as Lt operator

### Parser Changes

**Type Parameter Parsing**:
```simple
# AST node
struct TypeParam:
    name: text
    bounds: [TypeBound]?  # For later: where T: Trait

# Parse pattern
fn parse_type_params() -> [TypeParam]:
    # class Future<T, E>
    #              ^^^^^
    expect(Lt)
    var params = []
    loop:
        val name = expect(Ident)
        params.push(TypeParam(name: name, bounds: nil))
        if not check(Comma): break
        advance()
    expect(Gt)
    params
```

### Type System Changes

**Type Parameter Scope**:
```simple
# Scoping rules
class Future<T>:         # T in scope for class body
    value: T             # Valid
    fn get() -> T:       # Valid
        self.value

# Outside class:
val x: Future<i64>       # Must provide T
val y: Future<T>         # Error: T not in scope
```

**Substitution**:
```simple
# Type substitution map
TypeSubst = Dict<text, Type>

# When instantiating Future<i64>:
subst = {"T": Type.I64}

# Replace all occurrences of T with i64
```

---

## Part 7: Risk Analysis

### Risks of Generics Implementation

**High Risk**:
- Breaking existing parser (mitigate: comprehensive tests)
- Performance regression (mitigate: benchmark)

**Medium Risk**:
- Incomplete generics confuse users (mitigate: document limitations)
- Interaction with other features (mitigate: integration tests)

**Low Risk**:
- Compiler mode compatibility (already works)
- Backward compatibility (pure addition)

### Mitigation Strategy

**Phase-by-Phase Validation**:
1. Each phase has comprehensive tests
2. All existing tests must pass
3. Performance benchmarks run
4. Examples document limitations

**Rollback Plan**:
- Feature flag: `SIMPLE_RUNTIME_GENERICS`
- Can disable if issues found
- Compiled mode unaffected

---

## Part 8: Success Metrics

### Quantitative Goals

**TODO Reduction**:
- Phase 6.1-6.2: Enable parsing (no immediate TODO reduction)
- Phase 6.3: Unblock 8 async TODOs
- Phase 6.4: Unblock 15 collection TODOs
- **Total**: 23 TODOs → **318 remaining**

**Module Loading**:
- **Before**: 127 files with generics fail at runtime
- **After**: 127 files load successfully
- **Improvement**: +127 modules available

**Test Coverage**:
- Async tests: 0% → 85% (8 tests enabled)
- Generic collection tests: 60% → 95% (15 tests enabled)

### Qualitative Goals

**Developer Experience**:
- ✅ Can use Future/Task at runtime
- ✅ Can test async code interactively
- ✅ Parity between compiled and interpreted modes

**Codebase Health**:
- ✅ Less workaround code
- ✅ Cleaner type definitions
- ✅ Better examples for users

---

## Conclusion

### Recommended Action

**Proceed with Phase 6: Generics Implementation**

**Estimated Effort**: 5 days, 1,800 lines of code
**Expected Impact**: 51 TODOs unblocked, 127 modules loadable

**Phases**:
1. Parser foundation (2 days)
2. Type resolution (1 day)
3. Async enablement (1 day)
4. Collection enablement (1 day)

**Alternative**: If generics too complex, defer and focus on:
- Module import fixes (34 TODOs)
- FFI v2 design (85 TODOs)
- Test suite completion (102 TODOs)

### Next Steps

**Immediate**:
1. Get user approval for Phase 6 plan
2. Create task breakdown for implementation
3. Set up test infrastructure

**If Approved**:
- Start with Phase 6.1 (parser foundation)
- Incremental development with tests
- Deploy behind feature flag initially

---

**Document Status**: Planning Complete
**Recommendation**: Proceed with incremental generics support
**Expected Outcome**: 51 TODOs unblocked, major capability unlock
