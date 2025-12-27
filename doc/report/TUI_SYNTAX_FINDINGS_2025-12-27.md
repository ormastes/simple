# TUI Simple Library - Syntax Findings

**Date**: 2025-12-27
**Status**: Syntax patterns identified through interpreter testing

## Summary

Tested Simple interpreter with TUI library files to identify syntax issues. Found specific patterns that work and don't work in Simple language.

## Syntax Test Results

### ✅ Working Syntax

1. **Single-line strings**: `"text"`
2. **Array literals**: `[0, 0, 0, 0]`
3. **Public functions**: `pub fn name() -> T:`
4. **Tuple return types**: `-> (bool, str)`
5. **Tuple destructuring**: `let (success, msg) = func()`
6. **Method calls**: `s.len()`, `s.as_ptr()`
7. **Module imports**: `use module.path.*`

### ❌ Not Working Syntax

1. **Rust-style array initialization**: `[0u8; 4096]`
   - Error: `Unexpected token: expected RBracket, found Semicolon`
   - **Fix**: Use `alloc[u8](4096)` instead

2. **Python-style array repetition**: `[0] * 10`
   - Parses but semantic error: `expected int, got Array([Int(0)])`
   - **Fix**: Use `alloc[T](size)` or explicit literal `[0, 0, 0, ...]`

3. **Triple-quoted strings**: `"""multi-line text"""`
   - Error: `Unexpected token: expected expression, found Error("Unterminated f-string")`
   - **Fix**: Use string concatenation with `\n` or single-line docstrings

4. **FFI module access**: `ffi.call("function")`
   - Status: Not yet tested, pattern unclear
   - **Research needed**: How to call FFI functions in Simple

## Correct Syntax Patterns

### Buffer Allocation

**Incorrect**:
```simple
let mut result_buffer = [0u8; 4096]
```

**Correct** (from `simple/std_lib/src/core/string.spl:46`):
```simple
let result_buffer = alloc[u8](4096)
```

### Multi-line Strings

**Incorrect**:
```simple
return """Help text
Line 2
Line 3"""
```

**Correct**:
```simple
return "Help text\nLine 2\nLine 3"
```

Or use string concatenation:
```simple
return "Help text\n" +
       "Line 2\n" +
       "Line 3"
```

### Docstrings

**Incorrect**:
```simple
fn execute_code(code: String) -> String:
    """Execute Simple code via Rust Runner"""
    # ...
```

**Correct** (use single-line comment or omit):
```simple
fn execute_code(code: String) -> String:
    # Execute Simple code via Rust Runner
    # ...
```

## Files Requiring Fixes

### 1. `simple/std_lib/src/repl/__init__.spl` (45 lines)

**Issues**:
- Line 18, 38: `[0u8; 4096]` → `alloc[u8](4096)`
- FFI call pattern needs verification

**Changes needed**:
```simple
# Before:
let mut result_buffer = [0u8; 4096]

# After:
let result_buffer = alloc[u8](4096)
```

### 2. `simple/app/repl/main.spl` (160 lines)

**Issues**:
- Line 19: Triple-quoted docstring
- Lines 34-61: Triple-quoted help text

**Changes needed**:
```simple
# Before:
fn execute_code(code: String) -> String:
    """Execute Simple code via Rust Runner and return the result"""

# After:
fn execute_code(code: String) -> String:
    # Execute Simple code via Rust Runner and return the result

# Before:
fn show_help() -> String:
    return """Simple REPL Help
================
...
"""

# After:
fn show_help() -> String:
    return "Simple REPL Help\n" +
           "================\n" +
           "\n" +
           "Commands:\n" +
           "  exit()         - Exit the REPL\n" +
           # ... etc
```

### 3. `simple/std_lib/src/ui/tui/backend/ratatui.spl` (330 lines)

**Issue**: `expected identifier, found Assign`

**Needs investigation**: Specific line causing error not yet identified

### 4. `simple/std_lib/src/ui/tui/widgets/line_editor.spl` (260 lines)

**Issue**: `expected Fn, found DocComment("Create a new LineEditor")`

**Fix**: Remove or convert triple-quoted docstrings to comments

## Next Steps

1. **Immediate fixes**:
   - Replace `[T; N]` with `alloc[T](N)`
   - Replace triple-quoted strings with concatenation
   - Remove triple-quoted docstrings

2. **Research required**:
   - FFI call syntax in Simple
   - Module import patterns for FFI
   - Verify method call patterns (`.as_ptr()`, `.len()`)

3. **Testing approach**:
   - Fix files incrementally
   - Test each file with interpreter after changes
   - Validate with `./target/debug/simple <file>.spl`

## Reference Examples

Working Simple code that uses correct patterns:
- `simple/std_lib/src/core/string.spl` - `alloc[u8](size)` pattern
- `simple/std_lib/test/unit/core/arithmetic_spec.spl` - Working test structure
- `simple/std_lib/test/unit/core/pattern_matching_spec.spl` - Working patterns

## Estimated Effort

With these findings, fixing the syntax issues should take **2-3 hours**:
- 30 min: Fix buffer allocations (2 files)
- 60 min: Fix triple-quoted strings (2 files)
- 30 min: Research and fix FFI patterns
- 30 min: Test and debug remaining issues

**Total**: All syntax patterns identified, fixes are straightforward replacements.

---

**Status**: ✅ Syntax patterns documented
**Next**: Apply fixes to TUI library files
**Blocker**: FFI call syntax still needs clarification
