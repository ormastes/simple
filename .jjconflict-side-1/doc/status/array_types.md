# Feature: Array Types (#41)

**Core Type Feature**
- **Importance**: 5/5
- **Difficulty**: 3/5
- **Status**: COMPLETED

## Goal

Enable array literal creation and element access:
```
let arr = [10, 20, 30]
main = arr[0] + arr[1]  # returns 30
```

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Added test `runner_handles_array_literals_and_indexing`
- Tests: literal indexing, variable index, expression index, arithmetic with elements, loop iteration

### Phase 2: Implementation (Green) - DONE
- Added `Expr::Index` handling in `evaluate_expr()` at `lib.rs:654`
- Evaluates receiver (array), index (integer), looks up field by string key
- Supports bounds checking with descriptive error

### Phase 3: Verify - DONE
- All 15 driver tests pass

## Files Modified

| File | Change |
|------|--------|
| `src/compiler/src/lib.rs` | Added `Expr::Index` case in `evaluate_expr()` |
| `src/driver/tests/runner_tests.rs` | Added array literal and indexing tests |

## Progress

- [x] Create status file
- [x] Write system test (TDD: Red)
- [x] Implement `Expr::Index` evaluation
- [x] Verify all tests pass (TDD: Green)

## Implementation Details

```rust
Expr::Index { receiver, index } => {
    let recv_val = evaluate_expr(receiver, env, functions, classes, enums)?;
    let idx_val = evaluate_expr(index, env, functions, classes, enums)?.as_int()?;
    if let Value::Object { class, fields } = recv_val {
        if class == "__array__" {
            let key = idx_val.to_string();
            fields
                .get(&key)
                .cloned()
                .ok_or_else(|| CompileError::Semantic(format!("array index out of bounds: {idx_val}")))
        } else {
            // Support generic object indexing by string key
            let key = idx_val.to_string();
            fields
                .get(&key)
                .cloned()
                .ok_or_else(|| CompileError::Semantic(format!("key not found: {key}")))
        }
    } else {
        Err(CompileError::Semantic("index access on non-array/object".into()))
    }
}
```

## What Now Works

```
let arr = [10, 20, 30]
main = arr[0]           # returns 10
main = arr[1 + 1]       # returns 30

let i = 2
main = arr[i]           # returns 30

let arr = [1, 2, 3, 4, 5]
let sum = 0
let i = 0
while i < 5:
    sum = sum + arr[i]
    i = i + 1
main = sum              # returns 15
```

## Notes

- Arrays are internally stored as `Value::Object { class: "__array__", fields: HashMap }` where keys are string indices ("0", "1", etc.)
- Index expressions are evaluated at compile-time (constant folding / interpretation)
- Pre-existing type inference test failure (`infers_let_and_function_return`) is unrelated to this feature
