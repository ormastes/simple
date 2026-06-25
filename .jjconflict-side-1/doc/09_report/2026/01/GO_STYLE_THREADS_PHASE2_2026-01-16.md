# Phase 2 Completion Report: Channel Receive Operator `<-`

**Date:** 2026-01-16
**Phase:** 2 - Syntax (`<-` Operator)
**Status:** ✅ Complete

## Summary

Successfully implemented the Go-style channel receive operator `<-` for Simple's concurrency system. The operator provides intuitive syntax for receiving values from channels while maintaining Simple's safety guarantees.

## Implementation Details

### 1. Lexer Changes

**File:** `src/parser/src/token.rs`
- Added `ChannelArrow` variant to `TokenKind` enum
- Token represents the `<-` operator at the lexical level

**File:** `src/parser/src/lexer/mod.rs`
- Modified `<` token handling to check for `-` first (highest priority)
- Ensures `<-` is tokenized as single token before `<` or `-` separately
- Proper disambiguation: `<-` vs `< -` (with space)

**File:** `src/parser/src/lexer_tests_syntax.rs`
- Added `test_arrow_operators()` to verify `<-` tokenization
- Added `test_channel_arrow_disambiguation()` with comprehensive cases:
  - `<-` → single token
  - `< -` → two tokens (Lt, Minus)
  - `a<-b` → three tokens (identifier, ChannelArrow, identifier)
  - `a < -b` → four tokens (comparison with negative)

### 2. AST Changes

**File:** `src/parser/src/ast/nodes/core.rs`
- Added `ChannelRecv` variant to `UnaryOp` enum
- Represents channel receive as a unary prefix operator
- Aligns with other prefix operators (Neg, Not, BitNot, Ref, RefMut, Deref)

### 3. Parser Changes

**File:** `src/parser/src/expressions/binary.rs`
- Added handling for `TokenKind::ChannelArrow` in `parse_unary()` function
- Recursively parses operand to support nested receives: `<-<-rx`
- Creates `Expr::Unary` with `UnaryOp::ChannelRecv` operator

**File:** `src/parser/tests/expression_tests.rs`
- Added three comprehensive test cases:
  1. `test_channel_receive_operator()` - basic `<-rx` parsing
  2. `test_channel_receive_in_assignment()` - `val x = <-rx` parsing
  3. `test_channel_receive_nested()` - `<-<-nested_rx` parsing
- All tests pass ✅

### 4. Tree-sitter Grammar

**File:** `simple/std_lib/src/parser/treesitter/grammar.spl`

**Token additions:**
- Added `ChannelArrow` to operator token list (line 29)
- Updated `is_operator()` method to include `ChannelArrow` (line 74)

**Grammar rules:**
- Added `unary_expr` rule to grammar rules map (line 232)
- Created `unary_expr_rule()` function supporting prefix operators
- Created `unary_op_rule()` listing: Minus, Not, ChannelArrow
- Updated `binary_expr_rule()` to call `unary_expr_rule()` instead of `primary_expr_rule()`
- Properly handles precedence: unary operators bind tighter than binary

### 5. Syntax Highlighting

**File:** `simple/std_lib/src/parser/treesitter/queries/highlights.scm`
- Added `<-` to special operators section (line 288)
- Highlighted as `@operator.special` (same category as `->`, `=>`, `::`)

## Usage Examples

### Basic Receive
```simple
val value = <-rx
```

### Nested Receive
```simple
val nested_value = <-<-double_rx
```

### In Expressions
```simple
if <-done_channel:
    print("Task completed")
```

### Combined with Send
```simple
tx.send(42)
val result = <-rx
```

## Test Results

All tests pass:
```
running 3 tests
test test_channel_receive_in_assignment ... ok
test test_channel_receive_nested ... ok
test test_channel_receive_operator ... ok
```

Lexer tests verify proper disambiguation of `<-` vs `< -`.

## Verification

### Compilation
```bash
cargo check --package simple-parser
# ✅ Finished `dev` profile [unoptimized + debuginfo]
```

### Tests
```bash
cargo test --package simple-parser test_channel_receive
# ✅ 3 passed; 0 failed; 0 ignored
```

## Design Notes

### LL(1) Compatibility
The `<-` operator is LL(1)-friendly because:
- Distinct token prevents ambiguity with `<` and `-`
- Lexer handles longest-match tokenization
- Parser recognizes it as unary prefix operator without lookahead

### Tooling Support
The `<-` operator is well-supported in existing tooling:
- **Tree-sitter:** Grammar rules added for parsing and highlighting
- **LSP:** Syntax highlighting queries recognize operator
- **IDEs:** Established pattern used by Go, R, Haskell, OCaml

### Precedence
Channel receive has unary operator precedence (higher than binary operators):
```simple
val x = <-rx + 1    # Parsed as: (<-rx) + 1
val y = <-rx * 2    # Parsed as: (<-rx) * 2
```

## Next Steps

Phase 3 will implement:
1. `go` keyword for spawning threads
2. Two spawn styles:
   - `go(args) \params: expr` (explicit parameters)
   - `go |captures| \: expr` (Go-style capture)
3. Lowering `go` expressions to `spawn_isolated()` calls
4. SSpec tests for `go` keyword

## Files Changed

### Core Parser
- `src/parser/src/token.rs` (+1 variant)
- `src/parser/src/lexer/mod.rs` (+5 lines)
- `src/parser/src/lexer_tests_syntax.rs` (+51 lines)
- `src/parser/src/ast/nodes/core.rs` (+1 variant)
- `src/parser/src/expressions/binary.rs` (+8 lines)
- `src/parser/tests/expression_tests.rs` (+57 lines)

### Tree-sitter
- `simple/std_lib/src/parser/treesitter/grammar.spl` (+32 lines)
- `simple/std_lib/src/parser/treesitter/queries/highlights.scm` (+1 line)

**Total:** 8 files modified, 156 lines added

## Conclusion

Phase 2 successfully implements the `<-` channel receive operator, providing Go-style syntax while maintaining Simple's safety guarantees. The implementation is:

- ✅ LL(1) parser compatible
- ✅ Properly disambiguated from `<` and `-`
- ✅ Fully tested with comprehensive test cases
- ✅ Integrated with tree-sitter grammar
- ✅ Syntax highlighting enabled
- ✅ Zero runtime overhead (compile-time syntax)

The operator is ready for use in Phase 3's `go` keyword implementation.
