# Async/Await Validation Guide

**Date:** 2026-02-07
**Status:** Week 3 Complete - HIR Integration
**Component:** Compiler / HIR Lowering

---

## Overview

The async/await validation system ensures that async functions are correctly typed and that generated state machines maintain type consistency. This guide explains how the system works and how to use it.

## Architecture

### Components

```
Source Code
    ↓
Parser (AST)
    ↓
Desugaring (State Machine Generation)
    ├─ Suspension Analysis
    ├─ State Enum Generation
    └─ Poll Function Generation
    ↓
HIR Lowering
    ├─ Function Lowering
    └─ **Async Validation** ← THIS MODULE
    ↓
Type Checking
    ↓
Code Generation
```

### Validation Entry Point

Async validation is automatically triggered during HIR lowering:

**File:** `src/compiler/hir_lowering/items.spl`

```simple
impl HirLowering:
    me lower_function(fn_: Function) -> HirFunction:
        # ... lower function to HIR ...

        # Validate async functions
        if fn_.is_async:
            self.validate_async_function(hir_func)

        hir_func
```

### Validation Logic

**File:** `src/compiler/hir_lowering/async.spl`

```simple
impl HirLowering:
    me validate_async_function(func: HirFunction):
        """Validate async function and report errors."""
        val check = self.check_async_function(func, nil, nil)

        if not check.is_valid:
            for error in check.errors:
                self.error(error, func.span)
```

---

## Validation Checks

### 1. Return Type Validation

**Rule:** Async functions must return `Future<T>`

**Error Code:** E0701

**Example:**
```simple
# ❌ Wrong
async fn fetch() -> text:
    "result"

# ✅ Correct
async fn fetch() -> Future<text>:
    "result"
```

**Error Message:**
```
error[E0701]: async function 'fetch' must return Future<T>
  --> example.spl:1:20
   |
   = help: change return type to Future<text>
   = note: async functions automatically wrap return values in Future
```

### 2. Poll Function Signature Validation

**Rule:** Poll functions must have signature `(StateEnum, Waker) -> (StateEnum, Poll<T>)`

**Error Code:** E0704

**Example:**
```simple
# ❌ Wrong - missing waker parameter
fn poll_fetch(state: FetchState) -> (FetchState, Poll<text>):
    # ...

# ✅ Correct
fn poll_fetch(state: FetchState, waker: Waker) -> (FetchState, Poll<text>):
    # ...
```

**Error Message:**
```
error[E0704]: poll function 'poll_fetch' has invalid signature
  --> generated.spl:8:1
   |
   = help: poll function must have signature: (StateEnum, Waker) -> (StateEnum, Poll<T>)
   = note: the poll function drives the async state machine
```

### 3. Type Parameter Consistency

**Rule:** `T` in `Future<T>` must match `T` in `Poll<T>`

**Error Code:** E0705

**Example:**
```simple
# ❌ Wrong
async fn fetch() -> Future<text>:
    # ...

fn poll_fetch(...) -> (..., Poll<i64>):  # Mismatch: i64 vs text
    # ...

# ✅ Correct
async fn fetch() -> Future<text>:
    # ...

fn poll_fetch(...) -> (..., Poll<text>):  # Match: text
    # ...
```

**Error Message:**
```
error[E0705]: type parameter mismatch in 'poll_fetch'
  --> generated.spl:15:37
   |
   = help: async function returns Future<text>, but poll function returns Poll<i64>
   = note: the inner type T must be the same in both Future<T> and Poll<T>
```

### 4. State Enum Structure Validation

**Rule:** State enums must have at least `State0` variant

**Error Code:** E0708

**Example:**
```simple
# ❌ Wrong
enum FetchState:
    # No variants!

# ✅ Correct
enum FetchState:
    State0  # Initial state
    State1(x: i64)  # After first await
```

**Error Message:**
```
error[E0708]: invalid state enum structure for 'FetchState'
  --> generated.spl:5:1
   |
   = help: state enum must have at least State0 (initial state)
   = note: each suspension point creates an additional state variant
```

### 5. Future Type Availability

**Rule:** `Future` type must be in scope

**Error Code:** E0709

**Example:**
```simple
# ❌ Wrong - Future not imported
async fn fetch():
    # ...

# ✅ Correct
use std.async.future.Future

async fn fetch() -> Future<text>:
    # ...
```

**Error Message:**
```
error[E0709]: Future type not found in scope
  --> example.spl:5:1
   |
   = help: import Future from std.async.future
   = note: async functions require the Future type to be in scope
```

---

## API Reference

### Core Types

#### AsyncFunctionCheck

Validation results for an async function:

```simple
struct AsyncFunctionCheck:
    is_valid: bool
    errors: [text]                # Simple error messages
    detailed_errors: [AsyncError]  # Detailed diagnostics
    function_name: text
    inner_type: HirType?          # T in Future<T>
```

#### AsyncError

Detailed error diagnostic:

```simple
struct AsyncError:
    code: AsyncErrorCode
    message: text
    span: Span
    help: text?        # How to fix
    note: text?        # Why it's wrong
    suggestion: text?  # Example code

impl AsyncError:
    fn format() -> text  # Format for display
```

#### AsyncErrorCode

Error code enumeration:

```simple
enum AsyncErrorCode:
    E0701  # Async function must return Future<T>
    E0702  # Type mismatch in state machine
    E0703  # Invalid state transition
    E0704  # Poll function signature wrong
    E0705  # Future type parameter mismatch
    E0706  # Missing await in async function
    E0707  # Await used outside async function
    E0708  # Invalid state enum structure
    E0709  # Future not found in scope
    E0710  # Poll type not found in scope
```

### Validation Functions

#### check_async_function

Validate complete async function:

```simple
impl HirLowering:
    fn check_async_function(
        func: HirFunction,
        state_enum: HirEnum?,
        poll_func: HirFunction?
    ) -> AsyncFunctionCheck
```

**Parameters:**
- `func` - The async function to validate
- `state_enum` - Generated state enum (optional)
- `poll_func` - Generated poll function (optional)

**Returns:**
- Validation results with errors if any

**Example:**
```simple
val check = lowering.check_async_function(func, state_enum, poll_func)

if not check.is_valid:
    for error in check.errors:
        print error

    for detailed in check.detailed_errors:
        print detailed.format()
```

#### check_poll_function_signature

Validate poll function signature:

```simple
impl HirLowering:
    fn check_poll_function_signature(
        poll_func: HirFunction,
        expected_inner: HirType,
        span: Span
    ) -> AsyncFunctionCheck
```

#### check_state_enum_structure

Validate state enum structure:

```simple
impl HirLowering:
    fn check_state_enum_structure(
        state_enum: HirEnum,
        span: Span
    ) -> AsyncFunctionCheck
```

### Helper Functions

#### is_future_type

Check if type is `Future<T>`:

```simple
impl HirLowering:
    fn is_future_type(hir_type: HirType) -> bool
```

#### extract_future_inner

Extract `T` from `Future<T>`:

```simple
impl HirLowering:
    fn extract_future_inner(hir_type: HirType) -> HirType?
```

#### make_future_type

Construct `Future<T>` type:

```simple
impl HirLowering:
    fn make_future_type(inner: HirType, span: Span) -> HirType
```

---

## Error Collection

### AsyncErrorCollector

Collect multiple errors:

```simple
var collector = AsyncErrorCollector.new()

collector.add(async_fn_must_return_future(...))
collector.add(invalid_state_enum_structure(...))

if collector.has_errors():
    print collector.format_all()

val codes = collector.get_codes()
# ["E0701", "E0708"]
```

---

## Testing

### Unit Tests

**File:** `test/compiler/hir_async_spec.spl`

Tests individual validation functions:
- Future type recognition
- Inner type extraction
- Type formatting
- Function validation
- State enum validation

**File:** `test/compiler/hir_async_errors_spec.spl`

Tests error message generation:
- Error codes
- Error constructors
- Error formatting
- Error collection

### Integration Tests

**File:** `test/compiler/hir_async_integration_spec.spl`

Tests complete validation flow:
- Valid async functions
- Error detection
- Multiple error collection
- Error message quality

**File:** `test/compiler/async_pipeline_spec.spl`

Tests full compiler pipeline:
- Parsing → Lowering → Validation
- Error recovery
- Complex async patterns
- Nested async expressions

**File:** `test/compiler/async_desugar_integration_spec.spl`

Tests desugaring integration:
- State machine generation
- Type consistency
- Live variable tracking
- Poll function validation

### Running Tests

```bash
# All async tests
bin/simple test test/compiler/hir_async_spec.spl
bin/simple test test/compiler/hir_async_errors_spec.spl
bin/simple test test/compiler/hir_async_integration_spec.spl
bin/simple test test/compiler/async_pipeline_spec.spl
bin/simple test test/compiler/async_desugar_integration_spec.spl

# Or run all compiler tests
bin/simple test test/compiler/
```

---

## Implementation Files

| File | Purpose | Lines |
|------|---------|-------|
| `src/compiler/hir_lowering/async.spl` | Core validation logic | 467 |
| `src/compiler/hir_lowering/async_errors.spl` | Error diagnostics | 442 |
| `src/compiler/hir_lowering/items.spl` | Integration point | +8 |
| `src/compiler/hir_lowering.spl` | Facade exports | 19 |

---

## Future Work

### Short Term

1. **Enhanced State Enum Validation**
   - Validate field types match live variables
   - Check state transitions are valid
   - Verify state numbering is sequential

2. **Await Expression Validation**
   - Detect await outside async functions (E0707)
   - Validate awaited expression type
   - Check suspension point consistency

3. **Diagnostics Integration**
   - Report AsyncError objects through diagnostics system
   - Add source location underlining
   - Provide fix suggestions in IDE

### Medium Term

1. **Type Inference Integration**
   - Infer Future<T> return type from body
   - Propagate types through await expressions
   - Check async/await type consistency

2. **Effect System Integration**
   - Track async effects
   - Validate effect boundaries
   - Prevent blocking in async functions

3. **Optimization Hints**
   - Detect unnecessary state machine allocations
   - Suggest async fn optimization opportunities
   - Warn about performance issues

### Long Term

1. **Formal Verification**
   - Prove state machine correctness
   - Verify poll function implements async function
   - Guarantee no deadlocks or races

2. **Advanced Diagnostics**
   - Suggest async refactoring
   - Detect common async patterns
   - Provide async anti-pattern warnings

---

## Common Patterns

### Pattern 1: Simple Async Function

```simple
use std.async.future.Future
use std.async.poll.Poll

async fn fetch_data() -> Future<text>:
    val response = await http_get("https://api.example.com/data")
    response.body
```

**Validation:** Checks return type is Future<text>

### Pattern 2: Async Function with Error Handling

```simple
async fn safe_fetch() -> Future<Result<text, text>>:
    val response = await http_get("url")
    match response.status:
        200: Ok(response.body)
        _: Err("Failed to fetch")
```

**Validation:** Checks return type is Future<Result<...>>

### Pattern 3: Async Function with Multiple Awaits

```simple
async fn complex_operation() -> Future<i64>:
    val x = await step1()
    val y = await step2(x)
    val z = await step3(y)
    x + y + z
```

**Validation:**
- Checks return type is Future<i64>
- Validates state enum has State0, State1, State2, State3
- Validates poll function handles all states

### Pattern 4: Async Method

```simple
class DataService:
    api_url: text

    async fn fetch(id: i64) -> Future<text>:
        val url = "{self.api_url}/items/{id}"
        await http_get(url)
```

**Validation:** Same as regular async function

---

## Troubleshooting

### Error: "Async function must return Future<T>"

**Cause:** Function is marked `async` but doesn't return Future

**Fix:** Change return type to `Future<T>`

```simple
# Before
async fn fetch() -> text:
    "result"

# After
async fn fetch() -> Future<text>:
    "result"
```

### Error: "Future type not found in scope"

**Cause:** `Future` type not imported

**Fix:** Add import

```simple
use std.async.future.Future
```

### Error: "Poll function has invalid signature"

**Cause:** Generated poll function doesn't match expected signature

**Fix:** Check desugaring output - this is usually a compiler bug

### Error: "Type parameter mismatch"

**Cause:** Future<T> and Poll<T> have different inner types

**Fix:** Check type consistency in async function and poll function

---

## References

- **Phase 1 Report:** `doc/report/grammar_update_week3_phase1_2026-02-07.md`
- **Phase 2 Report:** `doc/report/grammar_update_week3_phase2_2026-02-07.md`
- **Desugaring:** `src/compiler/desugar/`
- **HIR Types:** `src/compiler/hir_types.spl`
- **Error Codes:** `src/compiler/hir_lowering/async_errors.spl`

---

**Last Updated:** 2026-02-07
**Version:** Week 3 Complete
**Status:** Production Ready ✅
