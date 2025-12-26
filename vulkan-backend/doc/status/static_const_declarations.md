# Feature: Static/Const Declarations (#45)

**Core Type Feature**
- **Importance**: 4/5
- **Difficulty**: 3/5
- **Status**: COMPLETED

## Goal

Enable compile-time constants and static variables:
```
const MAX_SIZE = 100     # Compile-time constant, immutable
static counter = 0       # Global static, immutable by default
static mut total = 0     # Global static, mutable
```

## TDD Approach

### Phase 1: System Test (Red) - DONE
- Added test `runner_handles_static_const_declarations`
- Tests: const declaration, const arithmetic, const immutability, static declaration, static mut, static immutability

### Phase 2: Implementation (Green) - DONE
- Added `Const` and `Static` to TokenKind in token.rs
- Added keyword matching for "const" and "static" in lexer.rs
- Added ConstStmt and StaticStmt to AST
- Added `parse_const()` and `parse_static()` functions to parser
- Added Node::Const and Node::Static to exec_node in compiler
- Added const/static to type checker's first pass

### Phase 3: Verify - DONE
- All 23 driver tests pass
- All 26 interpreter tests pass

## Files Modified

| File | Change |
|------|--------|
| `src/parser/src/token.rs` | Added `Const`, `Static` to TokenKind |
| `src/parser/src/lexer.rs` | Added "const", "static" keyword matching |
| `src/parser/src/ast.rs` | Added ConstStmt, StaticStmt types |
| `src/parser/src/parser.rs` | Added `parse_const()`, `parse_static()`, pub handling |
| `src/compiler/src/lib.rs` | Added Node::Const, Node::Static handling in exec_node |
| `src/type/src/lib.rs` | Added const/static to first pass registration |
| `src/driver/tests/runner_tests.rs` | Added static_const_declarations test |

## Progress

- [x] Create status file
- [x] Add Const, Static tokens
- [x] Add lexer keyword matching
- [x] Add ConstStmt, StaticStmt to AST
- [x] Add parse_const(), parse_static() to parser
- [x] Add pub support for const/static
- [x] Add Node::Const, Node::Static to compiler
- [x] Add to type checker first pass
- [x] Write system test (TDD: Red)
- [x] Verify all tests pass (TDD: Green)

## Implementation Details

### TokenKind
```rust
Const,
Static,
```

### AST Types
```rust
pub struct ConstStmt {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub value: Expr,  // Required - must be evaluable at compile time
    pub is_public: bool,
}

pub struct StaticStmt {
    pub span: Span,
    pub name: String,
    pub ty: Option<Type>,
    pub value: Expr,  // Required
    pub is_mutable: bool,
    pub is_public: bool,
}
```

### Parser
```rust
fn parse_const(&mut self) -> Result<Node, ParseError> {
    self.expect(&TokenKind::Const)?;
    let name = self.expect_identifier()?;
    // Optional type annotation
    // Required value
    Ok(Node::Const(ConstStmt { ..., is_public: false }))
}

fn parse_static(&mut self) -> Result<Node, ParseError> {
    self.expect(&TokenKind::Static)?;
    let is_mutable = self.check(&TokenKind::Mut);
    // ...
    Ok(Node::Static(StaticStmt { ..., is_mutable, is_public: false }))
}
```

### Compiler exec_node
```rust
Node::Const(const_stmt) => {
    let value = evaluate_expr(&const_stmt.value, env, ...)?;
    env.insert(const_stmt.name.clone(), (value, false)); // Always immutable
    Ok(Control::Next)
}
Node::Static(static_stmt) => {
    let value = evaluate_expr(&static_stmt.value, env, ...)?;
    env.insert(static_stmt.name.clone(), (value, static_stmt.is_mutable));
    Ok(Control::Next)
}
```

## What Now Works

```
# Compile-time constants
const MAX = 100
const BASE = 10
const MULTIPLIER = 5
main = BASE * MULTIPLIER    # returns 50

# Const with type annotation
const SIZE: i64 = 256

# Const cannot be reassigned
const X = 10
X = 20    # Error: cannot assign to immutable variable 'X'

# Static variables (immutable by default)
static counter = 42

# Static mut variables
static mut total = 0
total = total + 1
total = total + 1
main = total    # returns 2

# Static (non-mut) cannot be reassigned
static counter = 10
counter = 20    # Error: cannot assign to immutable variable 'counter'

# Public const/static
pub const API_VERSION = 1
pub static mut request_count = 0
```

## Notes

- `const` declarations are always immutable (compile-time constants)
- `static` declarations are immutable by default
- `static mut` allows mutable global variables
- Both const and static require an initializer value
- Type annotations are optional (inferred from value)
- Works with existing mutability control from #3
