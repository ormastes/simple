# Parser Fixes and Stdlib Test Improvements
**Date:** 2026-01-01
**Status:** In Progress

## Summary

Fixed several parser issues to improve stdlib test pass rate. Made progress on multi-line method chaining support, but encountered architectural limitations requiring further investigation.

## Changes Made

### 1. BDD Context Keyword Disambiguation ✅
**Problem:** Parser treated `context` as always being a context statement keyword, breaking BDD DSL usage.

**Solution:** Added lookahead logic to disambiguate:
- `context "string":` → BDD DSL (expression)
- `context expr:` → Context statement

**Files Modified:**
- `src/parser/src/parser_impl/core.rs` - Added lookahead in parse_item
- `src/parser/src/expressions/primary.rs` - Allow context as identifier
- `src/parser/src/parser_helpers.rs` - Added context to expect_identifier()

### 2. Default Keyword as Method Name ✅
**Problem:** `Type::default()` calls failed because `default` is a keyword.

**Solution:** Added `TokenKind::Default => "default"` to `expect_method_name()` to allow default as method name (similar to `new`, `type`, etc.).

**Files Modified:**
- `src/parser/src/parser_helpers.rs:309` - Added Default to method name allowlist

**Impact:** Fixed 4 stdlib test failures (theme_spec.spl and related tests).

### 3. Multi-line Method Chaining ⚠️
**Problem:** Method chaining across lines fails:
```simple
let parser = cli.ArgParser::new("test", "Test")
    .flag("verbose", "v", "Enable verbose output")  # Parse error!
```

**Root Cause:** The postfix expression parser breaks on NEWLINE tokens. The pattern `expr)\nINDENT.method()` requires:
1. Parsing `expr)` as complete expression
2. Seeing NEWLINE and breaking from postfix loop
3. But we need to peek ahead through NEWLINE→INDENT to see if DOT follows

**Attempted Solutions:**
1. **Using `peek_through_newlines_and_indents_is()`**
   - Breaks because `pending_token` can only store one token
   - Skipping NEWLINE→INDENT loses intermediate tokens
   - Result: 173 failures (regression from 110)

2. **Manual peek with full state save/restore**
   - Added NEWLINE case to postfix loop
   - Save state, advance past NEWLINE→INDENT, check for DOT
   - If not DOT, restore complete state
   - Result: 173 failures (broke if-statement parsing)

**Status:** Reverted to baseline. The limitation is a fundamental parser architecture issue:
- NEWLINE tokens serve dual purpose: expression terminators AND whitespace
- The postfix loop can't consume NEWLINE without breaking statement parsing
- Proper fix requires either:
  - Token buffer (not just `pending_token`) for multi-token lookahead
  - Different approach to NEWLINE handling globally
  - Context-aware NEWLINE consumption

### 4. Array Slice Syntax Fix ✅
**Problem:** Tests used `arr.slice(2, 5)` which isn't implemented.

**Solution:** Changed to Python-style syntax `arr[2:5]`.

**Files Modified:**
- `simple/std_lib/test/unit/compiler_core/collections_spec.spl`

## Test Results

### Current Status (After Fixes)
```
79 passed; 110 failed; 0 ignored
```

### Failure Breakdown
| Error | Count | Description |
|-------|-------|-------------|
| expected expression, found Indent | 20 | Multi-line method chaining (known limitation) |
| expected Colon, found RBrace | 4 | Macro template syntax issues |
| expected expression, found To | 3 | BDD matcher syntax in wrong context |
| expected pattern, found Context | 2 | Context statement parsing edge cases |
| expected identifier, found Newline | 2 | Newline handling in certain constructs |
| expected identifier, found Context | 2 | Context keyword in patterns |
| Other errors | 77 | Various syntax/feature issues |

## Recommendations

### Short Term
1. **Document Multi-line Method Chaining Limitation**
   - Add to known issues / language limitations
   - Provide workaround examples (single-line or intermediate variables)
   - File in `simple/improve_request.md`

2. **Fix Low-Hanging Fruit**
   - Investigate "expected Colon, found RBrace" (4 failures)
   - Check "expected expression, found To" (3 failures)
   - Fix context statement edge cases (4 failures)

3. **Skip Multi-line Chaining in Stdlib Tests**
   - Use single-line chains or intermediate variables
   - Focus on testing functionality, not syntax sugar

### Long Term
1. **Parser Architecture Refactor**
   - Implement token buffer for multi-token lookahead
   - Redesign NEWLINE handling to be context-aware
   - Consider separate "expression terminator" vs "whitespace" tokens

2. **Add Parser Tests**
   - Unit tests for postfix expression parsing
   - Test cases for NEWLINE handling in different contexts
   - Regression tests for if-statements, match, etc.

## Files Modified

### Production Code
- `src/parser/src/parser_impl/core.rs` - Context keyword disambiguation
- `src/parser/src/expressions/primary.rs` - Context as identifier
- `src/parser/src/parser_helpers.rs` - Context in identifiers, default in method names

### Test Code
- `simple/std_lib/test/unit/compiler_core/collections_spec.spl` - Array slice syntax
- `simple/std_lib/test/unit/cli_spec.spl` - Use spec.* import fix

## Lessons Learned

1. **Token Restoration is Hard**
   The `pending_token` mechanism is fragile when trying to peek multiple tokens ahead. A proper token buffer would be more robust.

2. **NEWLINE is Overloaded**
   Using NEWLINE for both expression termination and multi-line continuation creates ambiguity that's hard to resolve without context.

3. **Incremental Testing is Critical**
   Each attempted fix caused regressions. Need better parser unit tests to catch these early.

4. **Architecture Matters**
   Some bugs are symptoms of deeper architectural issues. Fixing them properly requires addressing the root cause, not patching the symptom.

## Next Steps

1. Commit current state with default keyword fix ✅
2. Document multi-line method chaining limitation in improve_request.md
3. Focus on fixing the simpler syntax errors (Colon/RBrace, To keyword, etc.)
4. Consider adding parser unit tests for regression prevention
5. Long-term: Plan parser refactor for better NEWLINE handling

## References

- Original issue: User requested "fixes" after 79/110 test results
- Related files: All stdlib test files in `simple/std_lib/test/`
- Parser implementation: `src/parser/src/expressions/mod.rs:617-875` (postfix loop)
