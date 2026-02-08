# Test Fix Session - Phase 3a: TreeSitter Lexer (2026-02-08)

## Summary

**Goal:** Create std.parser.treesitter module and fix lexer tests
**Result:** ✅ **42/42 tests passing (100%)**
**Time:** ~30 minutes

## Module Already Existed

The `src/std/parser/treesitter.spl` module already existed with basic implementation, but needed API updates to match test expectations.

## Changes Made

### 1. Resolved Module Conflict

**Problem:** Duplicate treesitter module in wrong location
```
src/std/parser/treesitter.spl       (correct location)
src/std/src/parser/treesitter.spl   (duplicate, wrong location)
```

**Fix:** Renamed duplicate to `.backup` to prevent module loader confusion

### 2. Updated Span Structure

**Before:**
```simple
struct Span:
    start: i64
    end: i64
```

**After:**
```simple
struct Span:
    start_byte: i64
    end_byte: i64
    start_line: i64
    start_column: i64
```

Tests expected `.start_byte`, `.start_line`, `.start_column` fields.

### 3. Added Factory Function

**Added:**
```simple
fn lexer_new(source: text) -> Lexer:
    Lexer(source: source)

impl Lexer:
    static fn new(source: text) -> Lexer:
        lexer_new(source)
```

Tests use `Lexer.new(source)` pattern.

### 4. Updated Return Type

**Before:** `fn tokenize() -> [Token]`
**After:** `fn tokenize() -> Option<[Token]>`

Tests use `.unwrap()` which requires Option or Result wrapper.

### 5. Added Position Tracking

**New functions:**
```simple
fn compute_position(source: text, byte_pos: i64) -> (i64, i64):
    """Compute (line, column) from byte position"""
    # Counts newlines to track line numbers

fn make_span(source: text, start: i64, end_pos: i64) -> Span:
    """Create a Span with line/column info"""
```

All token creation now uses `make_span()` to include position info.

### 6. Fixed Inline Ternary Bug

**Before (broken):**
```simple
val kind = if has_dot: TokenKind.Float else: TokenKind.Integer
# ERROR: cannot assign to const 'kind' (inline ternary unreliable)
```

**After (working):**
```simple
var kind = TokenKind.Integer
if has_dot:
    kind = TokenKind.Float
```

Applied MEMORY.md guidance: "Inline ternary unreliable - use explicit if/return blocks"

### 7. Converted Tests

- Updated imports: `use std.parser.treesitter.{Lexer, Token, TokenKind, Span}`
- Converted all 42 `skip_it` to `it`
- Removed `@pending` and `@skip` markers

## Test Results

| Test Group | Tests | Status |
|-----------|-------|--------|
| Basic Tokenization | 8 | ✅ 100% |
| Operators | 11 | ✅ 100% |
| Delimiters | 6 | ✅ 100% |
| Expressions | 4 | ✅ 100% |
| Token Spans | 3 | ✅ 100% |
| Token Text | 3 | ✅ 100% |
| Whitespace | 2 | ✅ 100% |
| EOF | 2 | ✅ 100% |
| Complex Source | 3 | ✅ 100% |
| **Total** | **42** | **✅ 100%** |

## Verification

```bash
bin/simple test test/system/features/treesitter/treesitter_lexer_spec.spl

# Results:
✓ All tests passed! (42 tests, 165ms)
```

## Other TreeSitter Tests

Remaining treesitter test files (not fixed - require extensive implementation):
- treesitter_cursor_spec.spl (24 tests) - needs Cursor API
- treesitter_error_recovery_spec.spl (48 tests) - needs error handling
- treesitter_incremental_spec.spl (52 tests) - needs incremental parsing
- treesitter_query_spec.spl (33 tests) - needs Query API
- treesitter_tree_spec.spl (26 tests) - needs Tree/Node API

Total: 183 tests requiring full TreeSitter API implementation (multiple days of work)

## Files Modified

- `src/std/parser/treesitter.spl` - Updated API, added position tracking
- `test/system/features/treesitter/treesitter_lexer_spec.spl` - Fixed imports, converted skip_it
- `src/std/src/parser/treesitter_full.spl.backup` - Renamed duplicate module

## Key Learnings

1. **Duplicate modules cause conflicts** - Module loader picks wrong file
2. **Inline ternary is unreliable** - Use explicit if/else blocks
3. **Position tracking needed** - Tests expect line/column info, not just byte offsets
4. **Factory functions preferred** - `Type.new()` pattern via static methods

## Next Steps

Phase 3a complete (lexer only). Options:
- Phase 3b: failsafe module (53 tests) - NEW MODULE
- Phase 3c: table module (26 tests) - NEW MODULE
- Skip remaining treesitter tests (need full API, ~183 tests, multiple days)

**Total progress so far:**
- Phase 1c: concurrent (33/33) ✅
- Phase 2a: debug (98/98) ✅
- Phase 2b: database_resource (23/27) ✅ 85%
- Phase 3a: treesitter_lexer (42/42) ✅
- **Total: 196 tests fixed**
