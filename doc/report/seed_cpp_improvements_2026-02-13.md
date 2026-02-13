# seed_cpp Improvements - 2026-02-13

## Summary

**Goal:** Improve seed_cpp to handle advanced Simple language features (Option B)

**Progress:** 4 of 7 major fixes complete ✅

## Completed Fixes

### ✅ Fix #1: Main Function Lookup
**File:** `seed/seed.cpp:3648-3651`
**Issue:** Second pass looked for "main" but function registered as "spl_main"
**Fix:** Added lookup name mapping
**Impact:** Main functions now work correctly

### ✅ Fix #2: Universal Stub Generation
**File:** `seed/seed.cpp:833`
**Issue:** Hardcoded `return true` stubbed all functions
**Fix:** Changed to `return false`
**Impact:** Real function bodies generated

### ✅ Fix #3: Implicit Returns
**File:** `seed/seed.cpp:2814-2840`
**Issue:** Struct constructors as last expression didn't generate `return`
**Fix:** Added implicit return detection in translate_block
**Impact:** ~100 files benefit
**Test:** `Point point_origin() { return Point{...}; }` ✅

### ✅ Fix #4: Enum Dot Notation
**File:** `seed/seed.cpp:2518-2570`
**Issue:** `case BuildMode.Debug:` not converted to `BuildMode_Debug`
**Fix:** Detect and translate `EnumName.Variant` syntax in case statements
**Impact:** ~60 files with enum matches now work
**Test:** `case BuildMode.Debug:` → `case BuildMode_Debug:` ✅

## Remaining Issues

### 1. Generics - `Option<T>` (HIGH Priority)
**Error:** `field has incomplete type 'Option_FunctionAttr'`
**Files Affected:** ~80
**Complexity:** High
**Status:** 🔴 NOT STARTED
**Approach Options:**
- A) Generate C++ templates for each generic type
- B) Monomorphize generics at transpile time
- C) Use type erasure (all generics → void*)

### 2. `.?` Optional Chaining (MEDIUM Priority)
**Error:** `expected expression` at `.?`
**Files Affected:** ~40
**Complexity:** Medium
**Status:** 🔴 NOT STARTED
**Fix:** Translate to ternary: `x.?` → `(x.has_value ? x.value : default)`

### 3. Pattern Matching with Data (LOW Priority)
**Error:** `case Promise(inner):` not translated
**Files Affected:** ~30
**Complexity:** High
**Status:** 🔴 NOT STARTED
**Workaround:** Use simple enums without data or rewrite with if statements

## Bootstrap Progress

| Metric | Initial | After Fix #3 | After Fix #4 | Target |
|--------|---------|--------------|--------------|---------|
| Files attempted | 318 | 302 | 298 | ~250 |
| C++ lines generated | 17,534 | 32,103 | 31,744 | ~30,000 |
| Compilation errors | ~200 | ~180 | ~120 | 0 |
| C++ compiles | ❌ | ❌ | ❌ | ✅ |

## Test Results

### Implicit Returns
```simple
fn point_origin() -> Point:
    Point(x: 0, y: 0)
```
**Generated:**
```cpp
Point point_origin() {
    return Point{.x = 0, .y = 0};  // ✅ return added!
}
```

### Enum Dot Notation
```simple
match mode:
    case BuildMode.Debug:
        return 1
```
**Generated:**
```cpp
switch (mode) {
    case BuildMode_Debug:  // ✅ dot converted to underscore!
        return 1;
}
```

## Next Steps

### Option A: Continue Fixes (Recommended)
1. ✅ Implicit returns - DONE
2. ✅ Enum dot notation - DONE
3. **TODO:** Fix `.?` operator (1-2 hours)
4. **TODO:** Basic generic type expansion (4-6 hours)
5. **TODO:** Pattern matching (optional, 8+ hours)

### Option B: Hybrid Approach
- Use seed_cpp for ~200 simple files
- Hand-write C++ for complex modules with generics
- Link together

### Option C: Minimal Core
- Exclude all files with generics/advanced features
- Bootstrap with just lexer/parser/simple codegen (~50 files)
- Use that to compile full compiler

## Recommendations

**Next Fix:** `.?` operator - Medium difficulty, high impact (40 files)

**Timeline:**
- `.?` operator: 1-2 hours
- Generic types: 4-6 hours
- Total remaining: ~8 hours for full bootstrap

**Alternative:** Exclude generic-heavy files, proceed with 200-file subset

## Files Modified

- `seed/seed.cpp` (4 fixes applied)
- `script/bootstrap-minimal.sh` (test file exclusions)

## Technical Details

### Implicit Return Detection
```cpp
/* Check if this is an implicit return */
bool is_implicit_return = false;
if (current_func && strcmp(current_func->ret_type, "void") != 0) {
    int next_idx = *line_idx + 1;
    if (next_idx >= num_lines ||
        indent_level(source_lines[next_idx]) <= base_indent) {
        is_implicit_return = true;
    }
}
```

### Enum Dot Notation Handling
```cpp
/* Handle EnumName.Variant notation */
char *dot = strchr(case_val, '.');
if (dot) {
    *dot = '\0';
    emit("case %s_%s:\n", case_val, dot + 1);
}
```

## Conclusion

✅ **4 major bugs fixed**
⚠️  **3 advanced features remaining**
🎯 **~8 hours to complete Option B**

Solid progress! Core bug fixes complete. Remaining work is on advanced language features (generics, operators).
