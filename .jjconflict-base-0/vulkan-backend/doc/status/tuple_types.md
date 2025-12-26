# Feature: Tuple Types (#40)

**Core Type Feature**
- **Importance**: 4/5
- **Difficulty**: 2/5
- **Status**: COMPLETED

## Goal

Enable tuple literal creation and element access:
```
let t = (10, 20, 30)
main = t[0] + t[1]  # returns 30
```

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Added test `runner_handles_tuples`
- Tests: literal indexing, tuple arithmetic, nested usage, empty tuples

### Phase 2: Implementation (Green) - DONE
- Added `Expr::Tuple` handling in `evaluate_expr()` at `lib.rs:873`
- Added explicit `__tuple__` case in `Expr::Index` for better error messages

### Phase 3: Verify - DONE
- All 18 driver tests pass

## Files Modified

| File | Change |
|------|--------|
| `src/compiler/src/lib.rs` | Added `Expr::Tuple` case, updated `Expr::Index` for tuples |
| `src/driver/tests/runner_tests.rs` | Added tuple tests |

## Progress

- [x] Create status file
- [x] Write system test (TDD: Red)
- [x] Implement `Expr::Tuple` evaluation
- [x] Update `Expr::Index` for tuple support
- [x] Verify all tests pass (TDD: Green)

## What Now Works

```
let t = (10, 20, 30)
main = t[0]           # returns 10
main = t[1]           # returns 20
main = t[2]           # returns 30

let t = (2, 3, 4)
main = t[0] + t[1] * t[2]  # returns 14

let point = (5, 10)
let x = point[0]
let y = point[1]
main = x + y          # returns 15

let t = ()            # empty tuple works
main = 42
```

## Notes

- Tuples are internally stored as `Value::Object { class: "__tuple__", fields: HashMap }` where keys are string indices ("0", "1", etc.)
- Similar implementation to arrays but with class `__tuple__` for distinct error messages
