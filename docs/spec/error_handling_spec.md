# Error Handling (Result Type)

*Source: `simple/std_lib/test/features/control_flow/error_handling_spec.spl`*

---

# Error Handling (Result Type)

**Feature ID:** #35
**Category:** Control Flow
**Difficulty:** 3/5 (Intermediate)
**Status:** Complete

## Overview

Simple uses **algebraic data types** for error handling instead of exceptions. The `Result<T, E>` type
represents either success (`Ok(value)`) or failure (`Err(error)`), enabling explicit, type-safe error
handling without try/catch blocks.

Following Rust's philosophy, errors are values that must be explicitly handled. This approach makes
error paths visible in the type system and forces developers to consider failure cases.

**Key Concepts:**
- **Result<T, E>:** Sum type with `Ok(T)` for success, `Err(E)` for errors
- **Explicit handling:** Errors must be unwrapped, propagated, or handled
- **No exceptions:** No runtime panics from unhandled exceptions
- **? operator:** Concise early return for error propagation
- **Type-safe:** Compiler tracks which operations can fail

## Syntax

### Result Type

```simple
# Function that can fail
fn divide(a: i32, b: i32) -> Result<i32, text>:
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)
```

**Type Parameters:**
- `T` - Success value type
- `E` - Error value type (usually `text` or custom error type)

### Creating Results

```simple
# Success
val success: Result<i32, text> = Ok(42)

# Failure
val failure: Result<i32, text> = Err("something went wrong")
```

### Unwrapping Results

```simple
# unwrap() - panics if Err
val value = result.unwrap()  # ⚠️ Unsafe: panics on Err

# unwrap_or() - provides default on Err
val value = result.unwrap_or(0)  # Safe: returns 0 on Err

# is_ok() / is_err() - check without consuming
if result.is_ok():
    val value = result.unwrap()

# Match pattern for full control
val output = match result:
    Ok(v) => process(v)
    Err(e) => handle_error(e)
```

### Error Propagation with ?

```simple
fn calculate() -> Result<i32, text>:
    val x = divide(10, 2)?  # Auto-propagate errors
    val y = divide(x, 0)?   # Returns Err early if divide fails
    return Ok(y)
```

**Desugaring:**
```simple
# The ? operator desugars to:
    val x = match divide(10, 2):
        Ok(v) => v
    Err(e) => return Err(e)
```

## Runtime Representation

**Result Enum:**
```rust
pub enum RuntimeValue {
    Result {
        is_ok: bool,
        value: Box<RuntimeValue>,  // T or E
    },
    // ... other variants
}
```

**Implementation:**
```rust
// Ok variant
RuntimeValue::Result {
    is_ok: true,
    value: Box::new(success_value),
}

// Err variant
RuntimeValue::Result {
    is_ok: false,
    value: Box::new(error_value),
}
```

**Method Dispatch:**
- `is_ok()` → check `is_ok` field
- `is_err()` → check `!is_ok`
- `unwrap()` → return `value` if `is_ok`, else panic
- `unwrap_or(default)` → return `value` if `is_ok`, else `default`

## Comparison with Other Languages

| Feature | Simple | Rust | Go | Java | Scala |
|---------|--------|------|----|----|-------|
| Error type | `Result<T, E>` | `Result<T, E>` | `(T, error)` | Exceptions | `Try[T]`, `Either[L, R]` |
| Success | `Ok(value)` | `Ok(value)` | `(value, nil)` | Return value | `Success(value)` |
| Failure | `Err(error)` | `Err(error)` | `(zero, err)` | `throw Exception` | `Failure(err)` |
| Propagation | `?` operator | `?` operator | `if err != nil` | `throws` | `flatMap` |
| Unwrap | `.unwrap()` | `.unwrap()` | N/A | N/A | `.get` |
| No exceptions | ✅ Yes (planned) | ✅ Yes | ✅ Yes | ❌ No | ✅ Yes (by convention) |

**Philosophy:**
- Simple/Rust: Errors are values, explicit handling required
- Go: Multiple return values (value, error)
- Java: Exceptions with try/catch (implicit propagation)
- Scala: Functional error handling with Try/Either

## Common Patterns

### Early Return with ?
```simple
fn process_data() -> Result<i32, text>:
    val raw = read_file()?        # Propagate read errors
    val parsed = parse(raw)?      # Propagate parse errors
    val validated = validate(parsed)?  # Propagate validation errors
    return Ok(validated)
```

### Fallback with unwrap_or
```simple
fn get_config_value(key: text) -> i32:
    val result = read_config(key)
    return result.unwrap_or(42)  # Default if read fails
```

### Explicit Error Handling with Match
```simple
match divide(10, 2):
    Ok(value) =>
        print("Success: {value}")
    Err(msg) =>
        print("Error: {msg}")
        # Handle error case
```

### Error Conversion
```simple
fn operation() -> Result<i32, text>:
    match database_query():
        Ok(rows) => process_rows(rows)
        Err(db_err) => Err("Database error: {db_err}")
```

## Implementation Files

**Parser:** `src/parser/src/expressions/mod.rs` - Result literals, ? operator
**Interpreter:** `src/compiler/src/interpreter.rs` - Result evaluation
**Runtime:** `src/runtime/src/value/objects.rs` - Result enum representation
**Type Checker:** `src/compiler/src/type_checker.rs` - Result<T, E> type validation
**Tests:** `src/driver/tests/interpreter_advanced_features_tests.rs` - Error handling tests

## Related Features

- **Option Type (#TBD):** Similar pattern for nullable values (Some/None)
- **Match Expressions (#90):** Primary way to handle Results exhaustively
- **Enums (#15):** Result is an enum with Ok/Err variants
- **Panic (#TBD):** For unrecoverable errors (vs recoverable Result errors)

## Performance Characteristics

| Operation | Time | Notes |
|-----------|------|-------|
| Creating Result | O(1) | Box allocation for value |
| is_ok/is_err check | O(1) | Boolean field check |
| unwrap | O(1) | Field access or panic |
| ? operator | O(1) | Match + early return |
| Match on Result | O(1) | Pattern dispatch |

**Memory:** Result adds one boolean flag + box pointer overhead (~16 bytes)

## Limitations and Future Work

**Current Limitations:**
- No try/catch blocks (only Result types)
- No automatic error conversions (must map errors manually)
- No panic/recover mechanism
- No stack traces on errors
- Error types not constrained (can be any type)

**Planned Features:**
- Panic/catch for unrecoverable errors
- Error trait for structured error types
- Stack trace capture
- Automatic error conversion via `From` trait
- `try` blocks for grouping fallible operations
- Result combinators: `map`, `and_then`, `or_else`

## Error Handling Best Practices

**Do:**
- Use `Result` for operations that can fail
- Propagate errors with `?` when appropriate
- Provide meaningful error messages
- Use `unwrap_or` for safe defaults
- Match on Results for exhaustive handling

**Don't:**
- Use `unwrap()` in production code (prefer `unwrap_or` or match)
- Ignore errors (compiler should enforce)
- Use exceptions (not available/planned)
- Return generic error strings (use structured errors when possible)

## Creating Result Values

    Result values represent the outcome of operations that can succeed or fail.
    The Result type has two variants: `Ok(value)` for success and `Err(error)` for failure.

    **Syntax:**
    - Success: `Ok(value)`
    - Failure: `Err(error_message)`

    **Type:** `Result<T, E>` where T is success type, E is error type

    **Implementation:** Result is an enum with two variants, stored as RuntimeValue

**Given** a successful operation result
        **When** wrapping the value in Ok
        **Then** creates a Result with is_ok=true

        **Example:**
        ```simple
        val success = Ok(42)
        assert success.is_ok() == true
        ```

        **Runtime:** RuntimeValue::Result { is_ok: true, value: 42 }

**Given** a failed operation with error message
            **When** wrapping the error in Err
            **Then** creates a Result with is_ok=false

            **Example:**
            ```simple
            val failure = Err("failed")
            assert failure.is_err() == true
            ```

            **Runtime:** RuntimeValue::Result { is_ok: false, value: "failed" }

## Unwrapping Result Values

    Unwrapping extracts the success value from a Result. Simple provides multiple
    unwrapping methods with different safety guarantees:

    - `unwrap()` - Get value or panic (unsafe)
    - `unwrap_or(default)` - Get value or return default (safe)
    - Pattern matching - Full control (safest)

    **Safety Ranking:**
    1. Match (safest - forces handling both cases)
    2. unwrap_or (safe - no panic possible)
    3. unwrap (unsafe - can panic)

**Given** a Result with Ok variant
        **When** calling unwrap()
        **Then** returns the wrapped value

        **Example:**
        ```simple
        val result = Ok(100)
        val value = result.unwrap()
        assert value == 100
        ```

        **Warning:** unwrap() panics on Err variant
        **Best Practice:** Use only when certain Result is Ok

**Given** a Result with Err variant
            **When** calling unwrap_or(default)
            **Then** returns the default value

            **Example:**
            ```simple
            val result = Err("error")
            val value = result.unwrap_or(0)
            assert value == 0  # Default returned
            ```

            **Safety:** No panic - always returns a value
            **Use Case:** Configuration values, optional features with defaults

## Checking Result Status

    Before unwrapping, you can check whether a Result is Ok or Err using
    `is_ok()` and `is_err()` methods. This enables conditional handling.

    **Methods:**
    - `is_ok()` - Returns true if Result is Ok variant
    - `is_err()` - Returns true if Result is Err variant

    **Pattern:** Check before unwrap to avoid panics

**Given** a Result value
        **When** calling is_ok()
        **Then** returns true for Ok, false for Err

        **Example:**
        ```simple
        val ok = Ok(1)
        val err = Err("bad")
        assert ok.is_ok() == true
        assert err.is_ok() == false
        ```

        **Use Case:** Conditional unwrapping
        ```simple
        if result.is_ok():
            val value = result.unwrap()
            process(value)
        ```

**Given** a Result value
            **When** calling is_err()
            **Then** returns true for Err, false for Ok

            **Example:**
            ```simple
            val ok = Ok(1)
            val err = Err("bad")
            assert ok.is_err() == false
            assert err.is_err() == true
            ```

            **Use Case:** Error logging
            ```simple
            if result.is_err():
                log_error(result.unwrap())
            ```

## Functions Returning Results

    Functions that can fail should return Result types. Callers must then
    explicitly handle the success and failure cases.

    **Pattern:**
    ```simple
    fn fallible_op() -> Result<T, E>:
        if success_condition:
            return Ok(value)
        else:
            return Err(error)
    ```

    **Benefit:** Errors are part of the function signature - callers know operation can fail

**Given** a function that returns Result
        **When** the function succeeds
        **Then** returns Ok(value)

        **Example:**
        ```simple
        fn divide(a: i32, b: i32) -> Result<i32, text>:
            if b == 0:
                return Err("division by zero")
            return Ok(a / b)

        val result = divide(10, 2)
        assert result.unwrap() == 5
        ```

        **Pattern:** Success path returns Ok

**Given** a function that can fail
            **When** the function encounters an error
            **Then** returns Err(error_message)

            **Example:**
            ```simple
            val result = divide(10, 0)
            assert result.is_err() == true
            assert result.unwrap() == "division by zero"
            ```

            **Pattern:** Error path returns Err with descriptive message
            **Best Practice:** Include context in error message
