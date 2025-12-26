# Feature: Pattern Matching (#12)

**Core Language Feature**
- **Importance**: 5/5
- **Difficulty**: 4/5
- **Status**: COMPLETED

## Goal

Enable pattern matching with `match` statement:
```
match x:
    1 =>
        result = 10
    2 =>
        result = 20
    _ =>
        result = 0
```

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Added test `runner_handles_pattern_matching`
- Tests: literal patterns, wildcard, variable binding, enum patterns, guards, match in functions

### Phase 2: Implementation (Green) - DONE
- Added `Node::Match` handling in `exec_node()` at `lib.rs:318`
- Implemented `exec_match()` function at `lib.rs:468-503`
- Implemented `pattern_matches()` helper at `lib.rs:508-636`
- Added match statement to module-level execution at `lib.rs:123`

### Phase 3: Verify - DONE
- All 16 driver tests pass
- All interpreter tests pass

## Files Modified

| File | Change |
|------|--------|
| `src/compiler/src/lib.rs` | Added exec_match, pattern_matches, Node::Match handling |
| `src/driver/tests/runner_tests.rs` | Added pattern matching tests |
| `src/type/src/lib.rs` | Added Node::Match and Expr::Match type checking |

## Progress

- [x] Create status file
- [x] Write system test (TDD: Red)
- [x] Implement exec_match function
- [x] Implement pattern_matches helper
- [x] Add Node::Match to exec_node
- [x] Add Match to evaluate_module top-level
- [x] Update type checker for Match
- [x] Verify all tests pass (TDD: Green)

## Patterns Supported

| Pattern | Example | Implementation |
|---------|---------|----------------|
| Wildcard | `_` | Always matches |
| Identifier | `n` | Binds value to name |
| Literal | `1`, `true` | Compares value |
| Enum | `Status::Ok` | Matches enum variant |
| Struct | `Point { x, y }` | Matches struct fields |
| Array | `[a, b, c]` | Matches array elements |
| Tuple | `(a, b)` | Matches tuple elements |
| Or | `1 \| 2` | Matches any pattern |
| Typed | `n: i32` | Pattern with type annotation |

## What Now Works

```
# Literal patterns
let x = 2
match x:
    1 =>
        result = 10
    2 =>
        result = 20
    _ =>
        result = 0
# result = 20

# Enum patterns
enum Status:
    Ok
    Error

let s = Status::Ok
match s:
    Status::Ok =>
        result = 1
    Status::Error =>
        result = 0
# result = 1

# Guards
let x = 10
match x:
    n if n > 5 =>
        result = 1
    _ =>
        result = 0
# result = 1

# In functions
fn classify(n):
    match n:
        0 =>
            return 0
        1 =>
            return 1
        _ =>
            return 2
```

## Notes

- Match arms use `=>` followed by newline and indented block
- Guards use `if` condition after pattern
- Pattern bindings are scoped to the arm body
- Enum matching checks both enum name and variant
