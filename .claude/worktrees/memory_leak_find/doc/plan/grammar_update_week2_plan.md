# Grammar Update - Week 2 Plan: State Machine Generation

**Date:** 2026-02-07
**Milestone:** Full Desugaring with State Machines
**Estimated Duration:** 1 week (5 days)
**Dependencies:** Week 1 complete ✅

---

## Overview

Week 2 will transform the simple desugaring from Week 1 into full-featured async/await state machine generation. This enables proper asynchronous execution with suspension and resumption.

**Current State (Week 1):**
```simple
# Simple transformation:
async fn fetch() -> text:
    val data = await get_data()
    data

# Becomes:
fn fetch() -> Future<text>:
    Future.ready({
        val data = block_on(get_data())
        data
    })
```

**Target State (Week 2):**
```simple
# Full state machine:
fn fetch() -> Future<text>:
    Future.from_generator(\state, waker:
        match state:
            case State0:  # Initial
                val future1 = get_data()
                (State1(future1), Poll.Pending)
            case State1(future1):  # After first await
                match future1.poll(waker):
                    case Ready(data):
                        (State2, Poll.Ready(data))
                    case Pending:
                        (State1(future1), Poll.Pending)
    )
```

---

## Goals

### Primary Deliverables

1. **State Machine Generator** (300-400 lines)
   - Suspension point identification
   - State enum generation
   - Poll loop generation
   - Waker handling

2. **Enhanced Desugaring** (200-300 lines)
   - Replace `Future.ready()` with state machines
   - Proper poll loops for await
   - State transition logic

3. **Test Suite** (30-40 tests)
   - State identification tests
   - State machine generation tests
   - Poll loop correctness tests
   - Integration tests

4. **Documentation** (800-1000 lines)
   - State machine design document
   - Transformation examples
   - Performance analysis

### Success Criteria

- ✅ Async functions generate proper state machines
- ✅ Await expressions create suspension points
- ✅ Poll loops handle Ready/Pending correctly
- ✅ Wakers registered and invoked properly
- ✅ All tests passing (100%)

---

## Architecture

### State Machine Components

**1. State Enum:**
```simple
enum FetchState:
    State0                           # Initial state
    State1(future: Future<Data>)     # Waiting on get_data()
    State2                           # Complete
```

**2. Poll Function:**
```simple
fn poll(state: FetchState, waker: Waker) -> (FetchState, Poll<text>):
    match state:
        case State0:
            # Execute until first await
            ...
        case State1(future):
            # Resume after first await
            ...
```

**3. Future Wrapper:**
```simple
Future.from_generator(\state, waker: poll(state, waker))
```

### Transformation Pipeline

```
Async Function
    ↓
Identify Suspension Points
    ↓
Generate State Enum
    ↓
Generate Poll Function
    ↓
Wrap in Future.from_generator
    ↓
Desugared Function
```

---

## Implementation Plan

### Phase 1: Suspension Point Analysis (Day 1, 8 hours)

**Goal:** Identify all suspension points in async function bodies

**Tasks:**
1. **Suspension Point Visitor** (3 hours)
   - Walk AST to find all `await` expressions
   - Track context (which block, which statement)
   - Assign suspension point IDs

2. **State Slot Analysis** (3 hours)
   - Determine which variables need to persist across suspension
   - Compute state slot layout
   - Handle variable lifetimes

3. **Tests** (2 hours)
   - Test simple functions (1 await)
   - Test complex functions (multiple awaits, nested)
   - Test control flow (if/else with awaits)

**Files:**
- `src/compiler/desugar/suspension_analysis.spl` (NEW, ~150 lines)
- `test/compiler/suspension_analysis_spec.spl` (NEW, 10 tests)

**Output:**
```simple
struct SuspensionPoint:
    id: i64
    await_expr: Expr
    context: BlockContext
    live_variables: [text]
```

### Phase 2: State Enum Generation (Day 2, 8 hours)

**Goal:** Generate state enum with variants for each suspension point

**Tasks:**
1. **Enum Generator** (4 hours)
   - Create enum with State0, State1, ... variants
   - Add fields to each variant for live variables
   - Generate constructor helpers

2. **State Transition Logic** (3 hours)
   - Generate state transition expressions
   - Handle control flow (if/else, match, loops)
   - Preserve local variable state

3. **Tests** (1 hour)
   - Test enum generation
   - Test state transition logic
   - Verify field preservation

**Files:**
- `src/compiler/desugar/state_enum.spl` (NEW, ~120 lines)
- `test/compiler/state_enum_spec.spl` (NEW, 8 tests)

**Output:**
```simple
struct StateEnum:
    name: text
    variants: [StateVariant]

struct StateVariant:
    name: text           # State0, State1, etc.
    fields: [Field]      # Live variables
```

### Phase 3: Poll Loop Generation (Day 3, 8 hours)

**Goal:** Generate poll() function that drives state machine

**Tasks:**
1. **Poll Function Generator** (4 hours)
   - Generate `fn poll(state, waker) -> (State, Poll<T>)`
   - Create match expression on state
   - Generate case arms for each state

2. **Ready/Pending Handling** (3 hours)
   - Wrap future.poll() calls
   - Handle Ready results (extract value, continue)
   - Handle Pending results (preserve state, return Pending)

3. **Tests** (1 hour)
   - Test poll function generation
   - Test Ready/Pending paths
   - Verify waker registration

**Files:**
- `src/compiler/desugar/poll_generator.spl` (NEW, ~180 lines)
- `test/compiler/poll_generator_spec.spl` (NEW, 10 tests)

**Output:**
```simple
struct PollFunction:
    state_param: text
    waker_param: text
    body: Block
```

### Phase 4: Integration & Testing (Day 4, 8 hours)

**Goal:** Integrate all components and test end-to-end

**Tasks:**
1. **Integrate into desugar_async_function** (3 hours)
   - Replace `Future.ready()` call
   - Wire up state machine components
   - Handle edge cases (no awaits, multiple returns)

2. **Comprehensive Testing** (4 hours)
   - End-to-end async function tests
   - Nested async calls
   - Error propagation
   - Performance benchmarks

3. **Bug Fixes** (1 hour)
   - Fix any integration issues
   - Handle edge cases discovered in testing

**Files:**
- `src/compiler/desugar_async.spl` (MODIFY, +100 lines)
- `test/compiler/async_state_machine_spec.spl` (NEW, 12 tests)

### Phase 5: Documentation & Polish (Day 5, 8 hours)

**Goal:** Document implementation and create completion report

**Tasks:**
1. **Design Documentation** (3 hours)
   - State machine architecture document
   - Transformation examples
   - Performance characteristics

2. **Code Documentation** (2 hours)
   - Add detailed comments to state machine generator
   - Document public APIs
   - Add usage examples

3. **Completion Report** (2 hours)
   - Week 2 completion summary
   - Test results
   - Performance metrics
   - Known limitations

4. **Commit and Push** (1 hour)
   - Create clean commits
   - Write descriptive commit messages
   - Push to repository

**Files:**
- `doc/design/async_state_machine.md` (NEW, ~600 lines)
- `doc/report/grammar_update_week2_complete.md` (NEW, ~800 lines)

---

## Detailed Implementation

### Suspension Point Analysis Algorithm

**Input:** Async function body (Block)
**Output:** List of suspension points

**Algorithm:**
1. Walk AST in execution order
2. For each `await` expression:
   - Assign suspension point ID (sequential)
   - Record expression and context
   - Compute live variables at this point
3. Return ordered list of suspension points

**Example:**
```simple
async fn example() -> text:
    val a = 1
    val b = await fetch1()  # SP0: live = [a]
    val c = await fetch2()  # SP1: live = [a, b]
    a + b + c

# Suspension points:
# SP0: await fetch1() - live variables: [a]
# SP1: await fetch2() - live variables: [a, b]
```

### State Enum Generation

**Input:** List of suspension points
**Output:** Enum definition

**Algorithm:**
1. Create State0 variant (initial state, no fields)
2. For each suspension point i:
   - Create State{i+1} variant
   - Add fields for live variables
   - Add field for future being awaited
3. Create terminal state (if needed)

**Example:**
```simple
# For example() above:
enum ExampleState:
    State0                              # Initial
    State1(a: i64, fut: Future<text>)  # After fetch1()
    State2(a: i64, b: text, fut: Future<text>)  # After fetch2()
```

### Poll Loop Generation

**Input:** Suspension points, state enum
**Output:** Poll function

**Algorithm:**
1. Generate function signature: `fn poll(state, waker) -> (State, Poll<T>)`
2. Generate match on state
3. For State0 (initial):
   - Execute code up to first await
   - Create future for first await
   - Return `(State1(vars, future), Poll.Pending)`
4. For State{i} (resumption after await i):
   - Poll the future
   - If Ready(value): extract value, continue to next await or return
   - If Pending: return `(State{i}(vars, future), Poll.Pending)`
5. For terminal state: return final value

**Example:**
```simple
fn poll_example(state: ExampleState, waker: Waker) -> (ExampleState, Poll<text>):
    match state:
        case State0:
            val a = 1
            val fut = fetch1()
            (State1(a: a, fut: fut), Poll.Pending)

        case State1(a, fut):
            match fut.poll(waker):
                case Ready(b):
                    val fut2 = fetch2()
                    (State2(a: a, b: b, fut: fut2), Poll.Pending)
                case Pending:
                    (State1(a: a, fut: fut), Poll.Pending)

        case State2(a, b, fut):
            match fut.poll(waker):
                case Ready(c):
                    val result = a + b + c
                    (State2(a, b, fut), Poll.Ready(result))
                case Pending:
                    (State2(a: a, b: b, fut: fut), Poll.Pending)
```

---

## Edge Cases

### No Await Expressions

If async function has no awaits, generate simple Future.ready() wrapper:

```simple
async fn immediate() -> i64:
    42

# Becomes:
fn immediate() -> Future<i64>:
    Future.ready(42)
```

### Multiple Return Points

Track return points separately, generate proper state transitions:

```simple
async fn conditional(flag: bool) -> text:
    if flag:
        return await fetch1()
    else:
        return await fetch2()

# Generate branching state machine
```

### Nested Async Calls

Flatten nested awaits into sequential suspension points:

```simple
async fn nested() -> text:
    await fetch(await get_url())

# Becomes two suspension points:
# SP0: await get_url()
# SP1: await fetch(url)
```

### Loops with Await

Generate loop state that re-enters same suspension point:

```simple
async fn loop_example():
    for item in items:
        await process(item)

# State machine loops back to same state
```

---

## Testing Strategy

### Unit Tests (20 tests)

- Suspension point identification (5 tests)
- State enum generation (5 tests)
- Poll loop generation (5 tests)
- Edge cases (5 tests)

### Integration Tests (10 tests)

- Simple async functions (2 tests)
- Complex async functions (3 tests)
- Control flow (3 tests)
- Error handling (2 tests)

### Performance Tests (5 tests)

- Large async functions (many awaits)
- Deep nesting
- Loop-heavy functions
- Compilation time benchmarks

---

## Success Metrics

**Code Quality:**
- All functions documented
- Clear separation of concerns
- Reusable components

**Test Coverage:**
- 100% test pass rate
- Edge cases covered
- Performance validated

**Performance:**
- Compilation overhead < 10ms per async function
- Generated code comparable to hand-written
- No memory leaks in state machines

**Documentation:**
- Complete design document
- Transformation examples
- Usage guide for language users

---

## Timeline

| Day | Phase | Deliverable | Status |
|-----|-------|-------------|--------|
| 1 | Suspension Analysis | suspension_analysis.spl + tests | ⏳ Planned |
| 2 | State Enum Gen | state_enum.spl + tests | ⏳ Planned |
| 3 | Poll Loop Gen | poll_generator.spl + tests | ⏳ Planned |
| 4 | Integration | async_state_machine_spec.spl | ⏳ Planned |
| 5 | Documentation | Design doc + completion report | ⏳ Planned |

**Total Estimate:** 5 days (40 hours)

---

## Dependencies

**Week 1 Complete:**
- ✅ Outline parser support
- ✅ Full parser integration
- ✅ Simple desugaring
- ✅ Test infrastructure

**External Dependencies:**
- `std.async.future.Future` library (assumed to exist)
- `std.async.runtime.Waker` type
- `std.async.poll.Poll` enum (Ready/Pending)

**If libraries don't exist:** Will create stub implementations for testing

---

## Risks & Mitigation

**Risk 1: AST complexity**
- Mitigation: Start with simple functions, add complexity incrementally

**Risk 2: State variable tracking**
- Mitigation: Use conservative approach (include all variables in state)

**Risk 3: Control flow complexity**
- Mitigation: Defer loop/match handling to later iterations if needed

**Risk 4: Runtime library missing**
- Mitigation: Create minimal stubs for testing

---

## Next Steps (Week 3)

After Week 2 completion:
- HIR lowering for Future<T> types
- Type checking for async functions
- Error messages for async/await misuse
- Optimization of generated state machines

---

**Plan Status:** Draft
**Review Date:** 2026-02-07
**Implementation Start:** Ready to begin
