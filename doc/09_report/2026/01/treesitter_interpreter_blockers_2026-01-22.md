# Tree-Sitter Interpreter Integration Blockers
**Date:** 2026-01-22
**Status:** Multiple syntax incompatibilities identified

---

## Summary

Tree-sitter module files cannot be loaded in the interpreter due to multiple syntax incompatibilities:

1. ✅ **FIXED:** `var fn` → `me` (mutable method syntax)
2. ✅ **FIXED:** `<>` generics → `[]` generics
3. ❌ **BLOCKER:** Array slicing syntax `str[start:end]` not supported
4. ❌ **BLOCKER:** Enum variant syntax (comma-separated without explicit values)
5. ❌ **BLOCKER:** Lambda syntax in some files
6. ⚠️ **WARNING:** `export use module.*` shows linter warnings

---

## Current Parse Errors

### 1. lexer.spl - Array Slicing
```
ERROR: expected RBracket, found Symbol("end_pos")
Location: Line 40
Code: val text = self.source[start_pos:end_pos]
```

**Issue:** String/array slicing with `[start:end]` syntax not supported in interpreter.

**Occurrences:**
- lexer.spl: lines 40, 176, 227 (3 instances)
- parser.spl: Unknown count

**Solution Options:**
- Use `.substring(start, end)` method instead
- Use `.slice(start, end)` method
- Implement slice syntax support in interpreter parser

### 2. parser.spl - Missing Expression
```
ERROR: expected expression, found Newline
```

**Possible Issues:**
- Empty method body
- Trailing comma in expression
- Incomplete statement before newline

### 3. tree.spl - Angle Bracket Generic
```
ERROR: expected identifier, found Lt
```

**Issue:** Still has unconverted `<>` generic syntax somewhere.

**Action:** Search and convert remaining `<>` to `[]`.

### 4. edits.spl - Unexpected LBrace
```
ERROR: expected identifier, found LBrace
```

**Possible Issues:**
- Struct literal syntax: `Point { x: 0, y: 0 }`
- Dict/map literal: `{key: value}`
- Lambda with braces: `fn() { ... }`

### 5. query.spl - Unexpected Fn
```
ERROR: expected identifier, found Fn
```

**Possible Issues:**
- Lambda syntax: `fn(x) ...` or `\x: ...`
- Nested function definition
- Function type in parameter

### 6. grammar.spl - Unexpected Comma
```
ERROR: expected identifier, found Comma
```

**Issue:** Enum variant definition with comma-separated variants:
```simple
enum TokenKind:
    Fn, Let, Mut, Return    # ❌ Not supported
```

**Should be:**
```simple
enum TokenKind:
    Fn                       # ✅ Supported
    Let
    Mut
    Return
```

---

## Syntax Compatibility Matrix

| Feature | Interpreter Parser | Tree-Sitter Files | Status |
|---------|-------------------|-------------------|--------|
| `val`/`var` variables | ✅ Supported | ✅ Used | ✅ Compatible |
| `me` mutable methods | ✅ Supported | ✅ Converted | ✅ Compatible |
| `var fn` methods | ❌ Not supported | ✅ Converted from | ✅ Fixed |
| `[]` generics | ✅ Supported | ✅ Converted to | ✅ Compatible |
| `<>` generics | ❌ Not supported | ✅ Mostly converted | ⚠️ Check remaining |
| Array slicing `[a:b]` | ❌ Not supported | ✅ Used extensively | ❌ **BLOCKER** |
| Enum comma variants | ❌ Not supported | ✅ Used | ❌ **BLOCKER** |
| Lambda `fn()` syntax | ⚠️ Partial | ✅ May be used | ⚠️ Check |
| `export use module.*` | ✅ Supported | ✅ Used | ⚠️ Lint warning |

---

## Recommended Fixes

### Priority 1: Array Slicing (BLOCKER)

**Files affected:** lexer.spl, parser.spl, possibly others

**Option A: Add .slice() method calls**
```bash
# Convert str[a:b] to str.slice(a, b)
find src/lib/std/src/parser/treesitter -name "*.spl" -exec sed -i \
  's/\([a-zA-Z_][a-zA-Z0-9_]*\)\[\([^:]*\):\([^]]*\)\]/\1.slice(\2, \3)/g' {} \;
```

**Option B: Add substring helper functions**
```simple
# In lexer.spl
fn substring(s: str, start: i64, end: i64) -> str:
    # Use FFI or available string method
    ...

# Then use: substring(self.source, start_pos, end_pos)
```

### Priority 2: Enum Variants (BLOCKER)

**Files affected:** grammar.spl (TokenKind enum)

**Solution:** Expand comma-separated variants to one-per-line
```bash
# Manual fix required - automatic conversion is complex
# Example:
#   Fn, Let, Mut
# To:
#   Fn
#   Let
#   Mut
```

### Priority 3: Remaining Syntax Issues

1. **tree.spl:** Find and convert remaining `<>` generics
2. **edits.spl:** Check struct literal syntax
3. **query.spl:** Check lambda syntax
4. **parser.spl:** Check for incomplete expressions

### Priority 4: Export Syntax (OPTIONAL)

Create conversion script as requested by user:
```bash
#!/bin/bash
# convert_exports.sh
find src/lib/std/src/parser/treesitter -name "*.spl" -exec sed -i \
  's/^export use /export /g' {} \;
```

**Note:** This may cause parse errors - test before committing.

---

## Testing Strategy

After each fix:

1. Test module loading:
```bash
./target/debug/simple -c "use parser.treesitter.{TreeSitterParser}; print('OK')"
```

2. Test constructor call:
```bash
./target/debug/simple test_ts_runtime.spl
```

3. Check for new parse errors:
```bash
./target/debug/simple test_ts_runtime.spl 2>&1 | grep "Failed to parse"
```

---

## Status

- ✅ Phase 1-6 grammar implementation: Complete (90%+ coverage)
- ✅ Verification script: All 76/76 components verified
- ✅ Syntax conversion (`var fn` → `me`): Complete
- ✅ Generics conversion (`<>` → `[]`): Mostly complete
- ❌ Array slicing: Not converted yet
- ❌ Enum variants: Not converted yet
- ❌ Module loading: Still failing

**Next Steps:**
1. Convert array slicing to method calls
2. Expand enum variants to one-per-line
3. Test module loading
4. Fix any remaining syntax issues
5. Activate test suite

---

**Estimated Time to Unblock:** 2-4 hours (primarily array slicing conversion)
