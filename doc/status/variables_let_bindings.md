# Feature: Variables & Let Bindings

**Feature #2 from feature.md**
- **Importance**: 5/5
- **Difficulty**: 2/5
- **Status**: COMPLETED

## Goal

Support variable declarations with `let` and variable references in expressions.

```
let x = 10
let y = 20
main = x + y    # returns 30
```

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Added test `runner_supports_variables`
- Tests: simple variable, two variables, variable in expression
- Tests variable referencing another variable
- Test failed initially: "unsupported expression type: Identifier"

### Phase 2: Implementation (Green) - DONE
- Added `Env` type alias for `HashMap<String, i32>`
- Modified `extract_main_value` to process statements in order
- Handle `Node::Let` to evaluate and store variable values
- Added `Expr::Identifier` case in `evaluate_expr` for lookups

### Phase 3: Verify - DONE
- All 66 workspace tests pass

## Files Modified

| File | Change |
|------|--------|
| `src/compiler/src/lib.rs` | Added Env, let handling, identifier lookup |
| `src/driver/tests/runner_tests.rs` | Added variable support tests |

## Progress

- [x] Status file created
- [x] System tests written
- [x] Variable environment implemented
- [x] Let statement handling
- [x] Identifier lookup in expressions
- [x] All tests passing (66/66)

## Implementation Details

```rust
type Env = HashMap<String, i32>;

fn extract_main_value(items: &[Node]) -> Result<i32, CompileError> {
    let mut env = Env::new();
    for item in items {
        match item {
            Node::Let(let_stmt) => {
                if let Some(value_expr) = &let_stmt.value {
                    let value = evaluate_expr(value_expr, &env)?;
                    if let Pattern::Identifier(name) = &let_stmt.pattern {
                        env.insert(name.clone(), value);
                    }
                }
            }
            Node::Assignment(assign) => {
                if name == "main" {
                    return evaluate_expr(&assign.value, &env);
                }
            }
            _ => {}
        }
    }
    Ok(0)
}

fn evaluate_expr(expr: &Expr, env: &Env) -> Result<i32, CompileError> {
    match expr {
        Expr::Identifier(name) => env.get(name).copied()
            .ok_or_else(|| CompileError::Semantic(format!("undefined variable: {}", name))),
        // ... other cases
    }
}
```

## What Now Works

```
let x = 42
main = x           # returns 42

let x = 10
let y = 20
main = x + y       # returns 30

let a = 5
main = a * a       # returns 25

let x = 7
let y = x + 3
main = y           # returns 10
```

## Next Features

- Unary operators (`-x`) - extends Feature #4
- Comparison operators (`<`, `>`, `==`) - for conditionals
- Control flow (`if/else`) - Feature #5
