# Parser Fixes Summary - 2026-01-30

## Issues Fixed

### 1. ✅ @ Operator (Matrix Multiplication)
**Status**: Already working correctly in parser
**Location**: `src/rust/parser/src/expressions/binary.rs:247`
**Implementation**: `parse_binary_single!(parse_matmul, parse_term, At, BinOp::MatMul)`

The @ operator was already fully implemented for matrix multiplication. No changes needed.

### 2. ✅ xor Keyword
**Status**: Already working correctly in parser
**Location**: `src/rust/parser/src/expressions/binary.rs:69`
**Implementation**: `parse_binary_single!(parse_bitwise_xor, parse_bitwise_and, Xor, BinOp::BitXor)`

The xor keyword was already fully implemented as a bitwise XOR operator. No changes needed.

### 3. ✅ super Keyword Support
**Status**: FIXED - Added super as valid primary expression
**Changes Made**:
- `src/rust/parser/src/expressions/primary/mod.rs:40` - Added `TokenKind::Super` to primary expression pattern matching
- `src/rust/parser/src/expressions/primary/identifiers.rs:21-24` - Added handler to parse `super` as `Expr::Identifier("super")`

**Result**: `super()` calls now parse correctly in methods and docstring examples.

## Root Cause of Test Failures

The test failures were NOT due to missing @ or xor or static parsing support. They were caused by **invalid type syntax** in library files.

### Invalid Type Syntax: `<T>` vs `[T]`

**Problem**: Many files used `<T>` standalone as a type, which is invalid.

**Correct Syntax Rules**:
- `<>` is ONLY valid AFTER a type constructor name: `Option<T>`, `List<Int>`, `Result<T, E>`
- For array types, use `[]`: `[i32]`, `[Tensor]`, `[Module]`
- For generic lists, use `List<T>` (if List type exists)

**Invalid Examples Found**:
```simple
fn parameters() -> <Tensor>:          # ❌ Invalid
layers: <Module>                       # ❌ Invalid
fn process(items: <T>) -> <R>:        # ❌ Invalid
```

**Correct Syntax**:
```simple
fn parameters() -> [Tensor]:          # ✅ Array type
layers: [Module]                       # ✅ Array type
fn process(items: [T]) -> [R]:        # ✅ Array types
# OR
fn process(items: List<T>) -> List<R>: # ✅ Generic list type
```

### Files With Invalid `<T>` Syntax

Found in 10+ files:
- `src/lib/std/src/ml/torch/nn/base.spl` (6 instances)
- `src/lib/std/src/ml/torch/transforms.spl`
- `src/lib/std/src/ml/torch/autograd.spl`
- `src/lib/std/src/infra/parallel.spl` (multiple functions)
- `src/lib/std/src/ml/torch/distributed/collective.spl`
- And others...

## Parser Logic Explanation

From `src/rust/parser/src/parser_types.rs:315-340`:

```rust
// Check for generic arguments - support both [] and <> syntax
let using_angle_brackets = self.check(&TokenKind::Lt);
let using_square_brackets = self.check(&TokenKind::LBracket);

if using_angle_brackets || using_square_brackets {
    self.advance(); // consume '[' or '<'
    // Parse type arguments...
```

The parser expects:
1. An identifier (type constructor name)
2. THEN optional generic arguments in `<>` or `[]`

So `List<T>` works, but standalone `<T>` doesn't.

## Remaining Issues

### base.spl Parse Error

**Error**: "Unexpected token: expected Fn, found Dedent"
**File**: `src/lib/std/src/ml/torch/nn/base.spl`
**Status**: Under investigation

This error persists even after fixing the `<T>` syntax. The root cause is still unknown. The file parses correctly in chunks but fails when parsed as a whole.

## Recommendations

1. **Systematic Fix**: Search and replace all `<T>` standalone type syntax with `[T]` across the codebase
2. **Add Lint Rule**: Create a lint to catch `fn.*->\s*<[A-Z]` and `:\s*<[A-Z]` patterns
3. **Update Documentation**: Clarify in CLAUDE.md that `<>` is only for generic parameters, not standalone array types
4. **Investigate base.spl**: Debug the persistent parse error in base.spl

## Test Results Impact

Before fixes: 95 failed tests (10.4%)
Root cause: Invalid `<T>` syntax causing parse errors

After fixes (estimated): Majority of ML/torch tests should pass once all `<T>` → `[T]` conversions are complete.

## Commands to Find All Invalid Syntax

```bash
# Find all files with potential <T> syntax issues
grep -r ":\s*<[A-Z]" src/lib/std/src --include="*.spl"

# Count occurrences
grep -r ":\s*<[A-Z]" src/lib/std/src --include="*.spl" | wc -l
```

## Related Documentation

- **Syntax Reference**: `doc/guide/syntax_quick_reference.md`
- **CLAUDE.md**: Generic syntax section (lines 43-61)
