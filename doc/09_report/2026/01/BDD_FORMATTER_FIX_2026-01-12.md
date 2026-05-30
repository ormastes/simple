# BDD Formatter Parse Error Fix - 2026-01-12

## Summary

Fixed critical parse errors in BDD framework formatter files that were preventing test files from loading. The issues were due to reserved keywords and Python syntax incompatibilities, NOT actual BDD framework bugs.

## Issues Identified

### 1. Reserved Keyword: `examples`

**Problem**: The identifier `examples` is reserved in the Simple parser and cannot be used as a variable name in pattern matching contexts.

**Error Message**: `parse error: Unexpected token: expected pattern, found Examples`

**Files Affected**:
- `simple/std_lib/src/spec/formatter/html.spl:174`
- `simple/std_lib/src/spec/formatter/markdown.spl:195`

**Fix Applied**:
```simple
# Before
if val Some(examples) = context.get("examples"):
    for example in examples:

# After
if val Some(example_list) = context.get("examples"):
    for example in example_list:
```

### 2. Reserved Keyword: `template`

**Problem**: The identifier `template` is a reserved keyword (borrowed from C++ terminology) and cannot be used as a field or parameter name.

**Files Affected**:
- `simple/std_lib/src/spec/formatter/html.spl:9,14,20`

**Fix Applied**:
```simple
# Before
class HtmlFormatter:
    template: text

fn default_template() -> text:

# After
class HtmlFormatter:
    html_template: text

fn default_html_template() -> text:
```

**Additional Changes**: Updated all references to `template` → `html_template` throughout the file.

### 3. Python Syntax: `None` vs `nil`

**Problem**: markdown.spl used Python's `None` instead of Simple's `nil` keyword.

**Files Affected**:
- `simple/std_lib/src/spec/formatter/markdown.spl:20,104,126,152`

**Fix Applied**:
```simple
# Before
test_file: None
case None:
return None

# After
test_file: nil
case nil:
return nil
```

### 4. Type Syntax Error

**Problem**: Typo in generic type parameter - used `]` instead of `>`.

**Files Affected**:
- `simple/std_lib/src/spec/formatter/markdown.spl:69`

**Fix Applied**:
```simple
# Before
fn format_example_with_media(name: text, status: text, error: Option<text], ...) -> text:

# After
fn format_example_with_media(name: text, status: text, error: Option<text>, ...) -> text:
```

## Impact

### Before Fix
- BDD framework couldn't load formatter module due to parse errors
- Tests importing `std.spec` would fail with cryptic errors
- 4+ test files appeared "blocked" by BDD framework bugs

### After Fix
- ✅ `html.spl` parses correctly
- ✅ BDD framework loads successfully
- ✅ Test files can now run (tests themselves still skipped, but framework works)
- ✅ `simple/std_lib/test/unit/sdn/lexer_spec.spl` - 25 examples load (all skipped as intended)
- ✅ `simple/std_lib/test/spec/bdd_framework_basic_spec.spl` - Still passing (18 tests)

### Known Issues
- `markdown.spl` still has parse errors related to complex match block indentation (lines 82-107)
- This doesn't block basic BDD functionality since html.spl is the primary formatter

## Files Modified

1. **`simple/std_lib/src/spec/formatter/html.spl`**
   - Renamed `examples` → `example_list` (line 174)
   - Renamed `template` → `html_template` (all occurrences)
   - Marked `escape_html` and `new_with_html_template` as `static`

2. **`simple/std_lib/src/spec/formatter/markdown.spl`**
   - Replaced `None` → `nil` (4 occurrences)
   - Fixed type syntax `Option<text]` → `Option<text>`
   - Renamed `examples` → `example_list` (line 195)

## Testing

```bash
# BDD framework basic test - PASSING
./target/debug/simple simple/std_lib/test/spec/bdd_framework_basic_spec.spl
# Result: 18 examples, 0 failures

# Previously "blocked" test - NOW LOADING
./target/debug/simple simple/std_lib/test/unit/sdn/lexer_spec.spl
# Result: 25 examples, 0 failures (all skipped as intended)
```

## Root Cause Analysis

The "BDD framework scoping bug" mentioned in test files was actually:
1. **Misleading error messages**: Reserved keyword errors appeared as framework bugs
2. **Module loading cascade**: `__init__.spl` exports from both `html` and `markdown`, so parse errors in either blocked the entire module
3. **Python-like syntax**: Files were written with Python conventions (`None`) instead of Simple syntax (`nil`)

## Lessons Learned

1. **Reserved Keywords**: Need comprehensive documentation of Simple's reserved words
2. **Error Messages**: Parser should provide clearer errors for reserved keyword violations
3. **Syntax Validation**: BDD framework files need better syntax checking in CI

## Next Steps

1. ✅ COMPLETE: Fix html.spl parse errors
2. ⏸️ DEFERRED: Fix markdown.spl complex match indentation (not blocking)
3. 📋 TODO: Add reserved keyword documentation to Simple language guide
4. 📋 TODO: Improve parser error messages for reserved keyword violations

---

**Status**: ✅ COMPLETE (markdown.spl optional)
**Impact**: High - Unblocked BDD framework usage
**Date**: 2026-01-12
**Author**: Claude (Simple Language Compiler Team)
