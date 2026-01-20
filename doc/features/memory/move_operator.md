# Move Operator - Explicit Ownership Transfer

**Status:** ✅ Implemented
**Version:** 1.0
**Date:** 2026-01-20

## Overview

The `move` keyword provides explicit ownership transfer for unique pointers in Simple's memory model. It prevents implicit copies that could violate memory safety rules, addressing the W1002 compiler warning.

## Syntax

```simple
val moved = move unique_ptr
```

The `move` operator is a **unary prefix operator** that:
- Takes an expression as its operand
- Evaluates to the same value as the operand
- Marks the transfer as explicit for the compiler
- Makes the original binding invalid after the move

## Motivation

Simple's memory model distinguishes between:
- **Shared pointers (`*T`)**: Reference-counted, copy-on-write, can be copied freely
- **Unique pointers (`&T`)**: Single ownership, move-only semantics
- **Mutable borrows (`&mut T`)**: Exclusive access, cannot be copied or moved

Without explicit `move`, copying a unique pointer would be unsafe:

```simple
val unique: &Data = new(&) Data(42)
val copy = unique  # ❌ W1002: Implicit unique copy
```

The compiler emits W1002 because implicit copies of unique pointers violate the single-ownership guarantee.

## Solution

Use explicit `move` to transfer ownership:

```simple
val unique: &Data = new(&) Data(42)
val moved = move unique  # ✅ OK: Explicit ownership transfer
# `unique` is now invalid and cannot be used
```

## Language Integration

### Parser

- **Token**: `move` keyword (TokenKind::Move)
- **AST**: UnaryOp::Move variant
- **Precedence**: Unary prefix operator (same level as `-`, `not`, `&`)

### Type System

- **Type preservation**: `move expr` has the same type as `expr`
- **No special typing**: Move is purely semantic, not a type transformation
- **Valid for all types**: Move can be applied to any expression, but is only meaningful for unique pointers

### Compiler

The compiler tracks move expressions during HIR lowering:

1. **Expression lowering** (`hir/lower/expr/operators.rs`):
   - UnaryOp::Move is recognized
   - Returns the operand's value unchanged
   - Acts as semantic marker only

2. **Statement lowering** (`hir/lower/stmt_lowering.rs`):
   - Checks if value expression is a move
   - Suppresses W1002 warning for explicit moves
   - Validates unique pointer semantics

3. **Warning suppression**:
   ```rust
   let is_explicit_move = Self::is_move_expr(ast_value);
   self.check_unique_copy(v, span, is_explicit_move);
   ```

### Interpreter

In the Simple interpreter (`simple/app/interpreter/expr/arithmetic.spl`):

```simple
case UnaryOp::Move:
    # Move is a semantic marker for explicit ownership transfer
    # In the interpreter, it's a no-op - ownership tracking happens elsewhere
    return Ok(val)
```

The interpreter treats `move` as a pass-through since:
- Ownership is tracked at compile time
- Runtime doesn't need special move handling
- Value is simply returned unchanged

## Usage Examples

### Basic Move

```simple
fn example_basic():
    val data = UniqueBox(42)
    val moved = move data
    # `data` cannot be used here
    print(moved.value)  # OK
```

### Function Arguments

```simple
fn take_ownership(data: UniqueBox):
    print("Received: {data.value}")

fn example_function():
    val data = UniqueBox(100)
    take_ownership(move data)  # Explicit transfer
    # `data` cannot be used here
```

### Collections

```simple
fn example_array():
    val item1 = UniqueBox(1)
    val item2 = UniqueBox(2)

    val arr = [move item1, move item2]
    # Items now owned by array
```

### Return Values

```simple
fn create_data() -> UniqueBox:
    val data = UniqueBox(777)
    return move data  # Explicit ownership transfer

fn example_return():
    val result = create_data()  # Receives ownership
```

### Pattern Matching

```simple
fn example_match():
    val maybe = Some(UniqueBox(999))

    match maybe:
        case Some(move data):
            print(data.value)  # Owns data in this branch
        case None:
            pass
```

## Comparison: Move vs Clone

| Aspect | `move value` | `value.clone()` |
|--------|--------------|-----------------|
| Ownership | Transfers | Creates new copy |
| Performance | Zero-cost | Allocates + deep copy |
| Original binding | Invalidated | Still valid |
| Use case | Ownership transfer | Need independent copy |
| Compiler warning | Satisfies W1002 | Satisfies W1002 |

Example:

```simple
val original = UniqueBox(42)

# Move: Transfer ownership (no copy)
val moved = move original
# `original` is now invalid

# Clone: Explicit copy (original still valid)
val cloned = original.clone()
# Both `original` and `cloned` are valid
```

## Design Decisions

### Why Unary Operator?

1. **Natural syntax**: `move x` reads clearly as "move x"
2. **Composability**: Works in any expression context
3. **LL(1) compatible**: `move` is a keyword prefix
4. **Precedence**: Unary operators have consistent precedence

### Why Not a Function?

- `move(x)` would require special compiler magic
- Functions can't invalidate their arguments
- Operator syntax is more idiomatic

### Why Not Automatic?

- Explicit is better than implicit (Python Zen)
- Makes ownership transfer visible in code
- Helps readers understand data flow
- Compiler can verify correctness

### Comparison with Rust

| Feature | Rust | Simple |
|---------|------|--------|
| Move syntax | Implicit | Explicit `move` |
| Copy trait | Opt-in via trait | Based on pointer kind |
| Borrow checker | Compile-time | Compile-time + warnings |
| Shared pointers | Rc/Arc | Built-in `*T` |
| Unique pointers | Box | Built-in `&T` |

Simple requires **explicit `move`** to make ownership transfer visible and prevent accidental copies.

## Compiler Warnings

### W1002: Implicit Unique Copy

**Before:**
```simple
val unique = new(&) Box(42)
val copy = unique  # ⚠️ W1002: Implicit unique copy
```

**After:**
```simple
val unique = new(&) Box(42)
val moved = move unique  # ✅ No warning
```

### Alternative: Explicit Clone

```simple
val unique = new(&) Box(42)
val cloned = unique.clone()  # ✅ No warning (explicit copy)
```

## Testing

### Unit Tests

- Parser tests: `src/parser/tests/`
- Type inference tests: `src/type/tests/`
- Compiler tests: `src/compiler/src/hir/lower/tests/`

### Feature Specs

- SSpec tests: `simple/std_lib/test/features/memory/move_operator_spec.spl`
- Examples: `simple/examples/memory/move_semantics.spl`

### Test Coverage

```bash
# Run all tests
make check

# Run memory-related tests
cargo test move
cargo test memory

# Run Simple interpreter tests
./target/debug/simple test simple/std_lib/test/features/memory/
```

## Implementation Files

### Parser
- `src/parser/src/ast/nodes/core.rs`: UnaryOp::Move enum variant
- `src/parser/src/expressions/binary.rs`: Move operator parsing
- `src/parser/src/token.rs`: TokenKind::Move token
- `src/parser/src/lexer/identifiers.rs`: "move" keyword recognition

### Compiler
- `src/compiler/src/hir/lower/expr/operators.rs`: HIR lowering for move
- `src/compiler/src/hir/lower/stmt_lowering.rs`: Move detection in let bindings
- `src/compiler/src/hir/types/expressions.rs`: UnaryOp conversion
- `src/type/src/checker_infer.rs`: Type inference for move

### Interpreter
- `simple/app/interpreter/expr/arithmetic.spl`: Move operator evaluation

## Future Work

1. **Move tracking**: Track which variables have been moved
2. **Use-after-move detection**: Error on using moved variables
3. **Partial moves**: Move individual fields from structs
4. **Move closures**: `move |x| expr` for closures that capture by value

## References

- **Memory Design**: doc/design/memory.md
- **Migration Guide**: doc/guide/memory_migration_guide.md
- **W1002 Warning**: src/compiler/src/hir/lower/memory_warning.rs
- **Memory Safety Plan**: doc/plan/manual_memory_safety_plan.md

## Related Issues

- Implemented in response to TODO comments in `src/compiler/src/hir/lower/stmt_lowering.rs:62,64`
- Addresses W1002 "implicit unique copy" warning
- Completes Simple's memory safety model
