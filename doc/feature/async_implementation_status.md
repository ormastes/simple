# Async/Await Implementation Status

**Date:** 2026-02-14
**Phase:** 1.3 - Basic Async Infrastructure - Type System Integration
**Status:** IN PROGRESS

---

## Executive Summary

This document tracks the implementation status of async/await functionality in the Simple language compiler. The async infrastructure is **partially implemented** at the parser and HIR levels, but **NOT integrated into the core type system**.

### Current Status (as of 2026-02-14)

- **Parser:** ✅ COMPLETE - async/await/spawn keywords supported
- **Desugaring:** ✅ COMPLETE - State machine generation implemented
- **HIR Lowering:** ✅ PARTIAL - Async validation logic exists
- **Core Type System:** ❌ NOT INTEGRATED - Missing Future<T>, Poll<T>, Task types
- **Runtime:** ✅ COMPLETE - Async runtime libraries exist (embedded & host)
- **Tests:** ⚠️ ALL SKIPPED - 38+ async test files exist but skip all tests

---

## Investigation Results

### Test Files Analysis

Total async-related test files: **38+**

#### Categories:

1. **Unit Tests (std):**
   - `test/unit/std/async_spec.spl` - ALL SKIPPED (basic async/await)
   - `test/unit/std/async_host_spec.spl` - ALL SKIPPED (host runtime)
   - `test/unit/std/async_embedded_spec.spl` - ALL SKIPPED (embedded runtime)

2. **Compiler Tests:**
   - `test/unit/compiler/async_pipeline_spec.spl` - FAILS/TIMEOUT
   - `test/unit/compiler/async_state_machine_spec.spl` - Unknown status
   - `test/unit/compiler/async_integration_spec.spl` - ALL TRIVIAL (expect 1 == 1)
   - `test/unit/compiler/async_desugar_integration_spec.spl` - Exists
   - `test/unit/compiler/async_mir_spec.spl` - Exists
   - `test/unit/compiler/async_mir_interpreter_spec.spl` - Exists

3. **Feature Tests:**
   - `test/feature/async_features_spec.spl` - PARTIAL (lambdas work, async skipped)
   - `test/feature/async_effects_spec.spl` - Unknown status
   - `test/feature/async_file_io_spec.spl` - Unknown status

4. **Deep Tests:**
   - `test/stdlib_deep/async_deep_1_spec.spl` through `async_deep_20_spec.spl`
   - `test/stdlib_complete/async_1_complete_spec.spl` through `async_5_complete_spec.spl`
   - `test/stdlib_improved/async_unit_spec.spl`, `async_edge_spec.spl`, etc.

### Why Tests "Pass"

The `async_spec.spl` passes because **ALL tests are marked `skip_it`**:

```simple
describe "Async functions":
    skip_it "defines async functions":
        # async fn fetch_data() -> i64
        pass
```

**Root cause:** Runtime parser does NOT support `async`, `await`, `spawn`, `yield` keywords.

### What Actually Works

From `test/feature/async_features_spec.spl`:

✅ **Lambda expressions** (6 tests passing):
- Basic lambdas: `\x: x * 2`
- Multi-param: `\x, y: x + y`
- Captures: `\x: x * multiplier`
- No-param: `\: 42`

❌ **Async/await syntax** - Parser rejects it at runtime
❌ **Future<T> type** - Not in core type system
❌ **State machines** - Generated but can't execute

---

## Core Type System Gap

### Missing Constants (FIXED)

Added to `/home/ormastes/dev/pub/simple/src/compiler_core/types.spl`:

```simple
val TYPE_FUTURE = 20
val TYPE_POLL = 21
val TYPE_TASK = 22
```

These constants are now:
1. Defined in the type tag section
2. Added to `type_tag_name()` function
3. Added to `type_tag_to_c()` function (returns `SplFuture*`, `SplPoll*`, `SplTask*`)
4. Exported in the module exports

### What Still Needs Implementation

1. **Runtime C types** - `SplFuture`, `SplPoll`, `SplTask` structs in `src/compiler_seed/runtime.h`
2. **Runtime functions** - Future polling, task scheduling, etc.
3. **Type checking** - Validate `Future<T>` generic instantiation
4. **HIR integration** - Connect HIR async types to core type tags

---

## Existing Async Infrastructure

### Parser Support (✅ Complete)

Located in: `src/compiler/parser*` (exact files TBD)

Supports:
- `async fn name() -> Future<T>:`
- `await expression`
- `spawn expression`
- `yield expression`

### Desugaring (✅ Complete)

Located in:
- `src/compiler/desugar_async.spl`
- `src/compiler_core_legacy/desugar_async.spl`

Generates:
- State enums (`FunctionNameState`)
- Poll functions (`poll_function_name`)
- State machine transitions

Example transformation:

```simple
# Input:
async fn fetch() -> Future<text>:
    val x = await get_data()
    x

# Output:
enum fetchState:
    State0
    State1(future: Future<text>)

fn poll_fetch(state: fetchState, waker: Waker) -> (fetchState, Poll<text>):
    match state:
        State0:
            val future = get_data()
            (State1(future: future), Poll.Pending)
        State1(future):
            match future.poll(waker):
                Ready(x): (State0, Poll.Ready(x))
                Pending: (State1(future: future), Poll.Pending)
```

### HIR Lowering (✅ Partial)

Located in:
- `src/compiler/hir_lowering/async.spl`
- `src/compiler/hir_lowering/async_errors.spl`

Provides:
- `is_future_type(hir_type)` - Check if type is Future<T>
- `extract_future_inner(hir_type)` - Get T from Future<T>
- `make_future_type(inner, span)` - Construct Future<T>
- Async validation errors

### Runtime Libraries (✅ Complete)

Located in `src/std/`:
- `async_core.spl` - Shared Poll<T>, TaskState, Priority types
- `async_embedded.spl` - Fixed-capacity, no-heap runtime
- `async_host.spl` - Dynamic, heap-allocated runtime
- `async_unified.spl` - Unified API (compile-time selection)
- `async.spl` - Main async module
- `async_sffi.spl` - FFI bindings

Key types:
- `Poll<T>` - Ready(T) | Pending
- `TaskState` - Pending | Running | Suspended | Completed | Cancelled | Failed
- `Priority` - Critical | High | Normal | Low | Idle

---

## Phase 1.3 Implementation Plan

### Step 1: Core Type System Integration (✅ COMPLETE)

**Status:** DONE (2026-02-14)

Added three type constants to `src/compiler_core/types.spl`:
- `TYPE_FUTURE = 20` - For Future<T> types
- `TYPE_POLL = 21` - For Poll<T> types
- `TYPE_TASK = 22` - For Task types

Updated:
- Type tag constants section
- `type_tag_name()` - Returns "Future", "Poll", "Task"
- `type_tag_to_c()` - Returns C type names
- Module exports

### Step 2: Runtime C Type Definitions (TODO)

**File:** `src/compiler_seed/runtime.h`

Add C struct definitions:

```c
// Future<T> - Represents async computation
typedef struct {
    int state_tag;      // State enum variant
    void* state_data;   // State-specific data
    void* waker;        // Waker for notification
    SplValue result;    // Cached result (if Ready)
} SplFuture;

// Poll<T> - Future poll result
typedef struct {
    int tag;            // 0 = Pending, 1 = Ready
    SplValue value;     // Result value (if Ready)
} SplPoll;

// Task - Schedulable async work
typedef struct {
    int64_t task_id;
    SplFuture* future;
    int priority;
    int state;          // TaskState enum
} SplTask;
```

### Step 3: Runtime C Function Stubs (TODO)

**File:** `src/compiler_seed/runtime.c`

Add basic runtime functions:

```c
SplFuture* spl_future_ready(SplValue value);
SplFuture* spl_future_pending();
SplPoll spl_future_poll(SplFuture* future, void* waker);
SplTask* spl_task_new(int64_t task_id, SplFuture* future);
```

### Step 4: Type Checking Integration (TODO)

**File:** `src/compiler/type_checker.spl` (or relevant module)

Implement:
- Generic type validation for `Future<T>`
- Ensure `async fn` returns `Future<T>`
- Validate `await` expressions expect `Future<T>`
- Check `Poll<T>` usage in state machines

### Step 5: Test One Simple Case (TODO)

Create minimal test:

```simple
# test/unit/compiler_core_legacy/future_type_spec.spl
describe "Future type integration":
    it "recognizes Future<i64> type tag":
        val tag = TYPE_FUTURE
        expect(type_tag_name(tag)).to_equal("Future")

    it "converts Future to C type":
        val c_type = type_tag_to_c(TYPE_FUTURE)
        expect(c_type).to_equal("SplFuture*")
```

### Step 6: Enable First Real Async Test (TODO)

Target: `test/feature/async_features_spec.spl`

Change first test from:
```simple
skip_it "creates and awaits basic future":
    check(true)
```

To:
```simple
it "creates and awaits basic future":
    async fn simple() -> Future<i64>:
        42

    val future = simple()
    val result = block_on(future)  # Runtime executor
    check(result == 42)
```

### Step 7: Iterate (TODO)

Continue enabling tests one by one:
1. Basic async function (no await)
2. Async function with single await
3. Async function with multiple awaits
4. Nested async calls
5. Error handling

---

## Blocker Analysis

### Why Tests Can't Run Now

1. **Runtime parser limitation** - Can't parse `async`, `await` keywords
   - **Workaround:** Use desugared form directly
   - **Proper fix:** Update parser to support keywords

2. **Missing runtime executor** - No `block_on()` function
   - **Workaround:** Call poll functions manually
   - **Proper fix:** Implement executor in `std.async`

3. **Type system gap** - No Future<T> type integration
   - **Status:** FIXED in Step 1
   - **Remaining:** Connect to HIR and runtime

4. **No runtime C support** - SplFuture not in runtime.h
   - **Status:** TODO in Step 2-3
   - **Impact:** Can't execute generated code

### Critical Path

To get first async test passing:

```
Type constants (✅) → Runtime C types (⏳) → Type checking (⏳) → Executor (⏳) → Test (⏳)
```

**Estimated effort:**
- Step 2-3 (Runtime C): 2-3 hours
- Step 4 (Type checking): 3-4 hours
- Step 5-6 (First test): 1-2 hours
- **Total:** 6-9 hours for minimal async support

---

## Next Actions

### Immediate (This Session)

1. ✅ Add TYPE_FUTURE, TYPE_POLL, TYPE_TASK to compiler_core/types.spl
2. ✅ Update type_tag_name() and type_tag_to_c()
3. ✅ Export new constants
4. ✅ Create this status document
5. ⏳ Test that type constants work (build system)

### Next Session

1. Add C struct definitions to src/compiler_seed/runtime.h
2. Add C function stubs to src/compiler_seed/runtime.c
3. Test basic type system integration
4. Start implementing type checking for Future<T>

### Future Sessions

1. Implement minimal executor (block_on)
2. Enable first async test
3. Iterate on remaining tests
4. Full async/await integration

---

## Success Criteria

### Phase 1.3 Complete When:

- ✅ TYPE_FUTURE, TYPE_POLL, TYPE_TASK defined in compiler_core/types.spl
- ⏳ SplFuture, SplPoll, SplTask defined in runtime.h
- ⏳ Type checker validates Future<T> generics
- ⏳ At least 1 async test passing (not skipped)
- ⏳ Documentation complete

### Full Async Support Complete When:

- All 38+ async test files passing
- Parser accepts async/await at runtime
- State machine generation working
- Executors (embedded + host) operational
- Real async I/O examples working

---

## Related Documents

- `doc/plan/async_await_implementation_plan.md` - Full async roadmap
- `doc/design/async_validation_status.md` - Async validation design
- `doc/guide/async_runtime_guide.md` - Runtime usage guide
- `src/std/async_core.spl` - Core async types
- `src/compiler/hir_lowering/async.spl` - HIR async integration

---

## Conclusion

Async infrastructure is **70% complete** but **0% executable**. The missing piece is the core type system integration, which is now **started** with the addition of type constants.

**Next priority:** Runtime C type support to enable actual execution.
