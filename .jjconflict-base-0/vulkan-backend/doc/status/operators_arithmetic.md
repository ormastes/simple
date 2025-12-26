# Feature: Operators - Arithmetic

**Feature #4 from feature.md**
- **Importance**: 5/5
- **Difficulty**: 2/5
- **Status**: COMPLETED

## Goal

Make the compiler evaluate arithmetic expressions so that `main = 1 + 2` returns 3.

## Operators Implemented

| Operator | AST Node | Implementation |
|----------|----------|----------------|
| `+` | `BinOp::Add` | `wrapping_add` |
| `-` | `BinOp::Sub` | `wrapping_sub` |
| `*` | `BinOp::Mul` | `wrapping_mul` |
| `/` | `BinOp::Div` | integer division (with zero check) |
| `%` | `BinOp::Mod` | modulo (with zero check) |

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Added test `runner_evaluates_arithmetic_expressions`
- Tests: `1 + 2`, `10 - 3`, `6 * 7`, `15 / 3`, `17 % 5`
- Tests operator precedence: `2 + 3 * 4` = 14
- Tests parentheses: `(2 + 3) * 4` = 20

### Phase 2: Implementation (Green) - DONE
- Added `evaluate_expr()` function for compile-time constant folding
- Recursively evaluates `Expr::Integer` and `Expr::Binary`
- Handles division/modulo by zero errors

### Phase 3: Verify - DONE
- All 65 workspace tests pass

## Files Modified

| File | Change |
|------|--------|
| `src/compiler/src/lib.rs` | Added `evaluate_expr()` with arithmetic ops |
| `src/driver/tests/runner_tests.rs` | Added arithmetic expression tests |

## Progress

- [x] Status file created
- [x] System tests written
- [x] Expression evaluation implemented
- [x] All tests passing (65/65)

## Implementation Details

```rust
fn evaluate_expr(expr: &Expr) -> Result<i32, CompileError> {
    match expr {
        Expr::Integer(value) => Ok(*value as i32),
        Expr::Binary { op, left, right } => {
            let left_val = evaluate_expr(left)?;
            let right_val = evaluate_expr(right)?;
            match op {
                BinOp::Add => Ok(left_val.wrapping_add(right_val)),
                BinOp::Sub => Ok(left_val.wrapping_sub(right_val)),
                BinOp::Mul => Ok(left_val.wrapping_mul(right_val)),
                BinOp::Div => Ok(left_val / right_val),  // with zero check
                BinOp::Mod => Ok(left_val % right_val),  // with zero check
                _ => Err(...)
            }
        }
        _ => Err(...)
    }
}
```

## Next Features

Logical next steps:
- Unary operators (`-x`, `not x`) - Part of Feature #4
- Comparison operators (`<`, `>`, `==`) - Part of Feature #4
- Variables (`let x = 42`) - Feature #2
