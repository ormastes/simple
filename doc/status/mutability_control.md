# Feature: Mutability Control (#3)

**Core Type Feature**
- **Importance**: 4/5
- **Difficulty**: 3/5
- **Status**: COMPLETED

## Goal

Enable explicit mutability declaration with `mut let`:
```
let x = 10          # immutable
mut let y = 20      # mutable
y = y + 1           # OK
x = x + 1           # Error: cannot assign to immutable variable
```

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Added test `runner_handles_mutability_control`
- Tests: immutable by default, mutable with `mut let`, reassignment of mutable vars

### Phase 2: Implementation (Green) - DONE
- Added `parse_mut_let()` function to parser for `mut let` syntax
- Changed `Env` type from `HashMap<String, Value>` to `HashMap<String, (Value, bool)>` where bool is `is_mutable`
- Updated all `env.get()` and `env.insert()` calls throughout the compiler
- Added mutability check in `Node::Assignment` handler
- Implemented manual `PartialEq` for `Value` due to `Arc<ActorHandle>` not implementing `PartialEq`

### Phase 3: Verify - DONE
- All 22 driver tests pass
- All 23 interpreter tests pass

## Files Modified

| File | Change |
|------|--------|
| `src/parser/src/parser.rs` | Added `parse_mut_let()` function, `TokenKind::Mut` handling |
| `src/compiler/src/lib.rs` | Changed Env type to track mutability, added assignment check |
| `src/driver/tests/runner_tests.rs` | Added mutability test, updated existing tests to use `mut let` |
| `src/driver/tests/interpreter_tests.rs` | Updated loop tests to use `mut let` |

## Progress

- [x] Create status file
- [x] Write system test (TDD: Red)
- [x] Add `parse_mut_let()` to parser
- [x] Change Env type to `HashMap<String, (Value, bool)>`
- [x] Update all env.get() and env.insert() calls
- [x] Add mutability check in Assignment handler
- [x] Implement manual PartialEq for Value
- [x] Update existing tests to use `mut let` for mutable variables
- [x] Verify all tests pass (TDD: Green)

## Implementation Details

### Parser: parse_mut_let()
```rust
fn parse_mut_let(&mut self) -> Result<Node, ParseError> {
    self.expect(&TokenKind::Mut)?;
    self.expect(&TokenKind::Let)?;
    let pattern = self.parse_pattern()?;
    let ty = if self.check(&TokenKind::Colon) { ... };
    let value = if self.check(&TokenKind::Assign) { ... };
    Ok(Node::Let(LetStmt { ..., is_mutable: true }))
}
```

### Env Type Change
```rust
// Before
type Env = HashMap<String, Value>;

// After
/// Variable environment for compile-time evaluation
/// Stores (value, is_mutable) pairs
type Env = HashMap<String, (Value, bool)>;
```

### Assignment Check
```rust
Node::Assignment(assign) if assign.op == AssignOp::Assign => {
    if let Expr::Identifier(name) = &assign.target {
        if let Some((_, is_mutable)) = env.get(name) {
            if !is_mutable {
                return Err(CompileError::Semantic(format!(
                    "cannot assign to immutable variable '{name}'"
                )));
            }
        }
        // ... update value, preserving mutability flag
    }
}
```

## What Now Works

```
# Immutable by default
let x = 10
# x = 20  # Error: cannot assign to immutable variable 'x'

# Mutable with mut let
mut let counter = 0
counter = counter + 1  # OK
counter = counter + 1  # counter is now 2

# Loops require mut let for counters
mut let sum = 0
mut let i = 0
while i < 5:
    sum = sum + i
    i = i + 1
main = sum  # returns 10
```

## Notes

- Variables are immutable by default, enforcing functional programming safety
- `mut let` explicitly opts into mutability
- Mutability is tracked at compile-time in the environment
- Error messages clearly indicate which variable cannot be assigned
