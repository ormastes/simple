# seed_cpp Main Function Fix - 2026-02-13

## Summary

Fixed two critical bugs in seed_cpp that prevented function bodies from being generated, particularly affecting `fn main() -> i32:`.

## Problems Solved

### Bug #1: Main Function Lookup Mismatch
**Location:** `seed/seed.cpp` lines 3648-3651
**Symptom:** Main function body always stubbed even when translation succeeded
**Root Cause:** Second pass extracts "main" from source but function was registered as "spl_main" in first pass

**Fix:**
```cpp
/* If function is "main", look for "spl_main" (renamed in first pass) */
const char *lookup_name = (strcmp(fname, "main") == 0) ? "spl_main" : fname;
FuncInfo *fi = find_func(lookup_name);
if (!fi) { continue; }
```

### Bug #2: Universal Stub Generation
**Location:** `seed/seed.cpp` line 833
**Symptom:** ALL function bodies stubbed, not just problematic ones
**Root Cause:** `output_has_problems()` had hardcoded `return true;` left over from development

**Fix:**
```cpp
/* Before: */
/* Stub ALL bodies for initial compilation pass */
return true;  // Always stubbed everything!

/* After: */
/* No problems detected - body is good! */
return false;
```

## Verification

### Test Case: bootstrap_main.spl
```simple
fn bootstrap_hello():
    print "Simple Bootstrap Compiler v0.1"
    print "Usage: core1 <file.spl>"

fn main() -> i32:
    bootstrap_hello()
    0
```

### Generated C++ (BEFORE fix):
```cpp
int32_t spl_main() {
    return 0; /* stub */
}
```

### Generated C++ (AFTER fix):
```cpp
void bootstrap_hello() {
    spl_println("Simple Bootstrap Compiler v0.1");
    spl_println("Usage: core1 <file.spl>");
}

int32_t spl_main() {
    bootstrap_hello();
    return 0;
}
```

### Runtime Test:
```bash
$ ./seed/build/seed_cpp src/compiler_core/bootstrap_main.spl > /tmp/test.cpp
$ clang++ -std=c++20 -O2 -o /tmp/test /tmp/test.cpp -Iseed -Lseed/build -lspl_runtime -lm -lpthread -ldl
$ /tmp/test
Simple Bootstrap Compiler v0.1
Usage: core1 <file.spl>
```

✅ **SUCCESS** - Both bugs fixed, main() generates real code!

## Impact on Full Bootstrap

### Minimal Bootstrap (1 file): ✅ Works
- `bootstrap_main.spl` compiles and runs successfully
- Generates real function bodies, not stubs
- Proves seed_cpp main() fix is complete

### Extended Bootstrap (302 files): ⚠️  Partial
After fixing main(), full bootstrap now reaches C++ compilation but hits **new** seed_cpp translation limitations:

1. **Option<T> generics** - `Option_FunctionAttr` incomplete type
2. **Trait system** - Complex trait code translation errors
3. **Pattern matching** - `case Promise(inner):` not translated
4. **`.?` operator** - Optional chaining syntax not handled
5. **Struct initialization** - Missing `return` statements

These are **translation limitations**, not main() bugs. Full compiler bootstrap requires either:
- Fixing seed_cpp to handle these patterns
- Creating simplified/stubbed versions for bootstrap
- Excluding advanced features from initial bootstrap

## Next Steps

1. **Immediate:** Document seed_cpp translation capabilities/limitations
2. **Short-term:** Create minimal bootstrap with just lexer/parser/codegen
3. **Long-term:** Incremental expansion or full seed_cpp improvement

## Files Modified

- `seed/seed.cpp` (2 bug fixes)
- `script/bootstrap-fixed.sh` (updated bootstrap script)
- `script/bootstrap-minimal.sh` (created, excludes complex features)

## Test Results

| Test | Files | Result |
|------|-------|--------|
| bootstrap_main.spl only | 1 | ✅ PASS |
| Minimal set (lexer/parser/ast) | 4 | ✅ Transpiles (functions stubbed) |
| Filtered bootstrap (exclude aop/traits) | 302 | ⚠️  Transpiles, C++ errors |
| Full bootstrap (all files) | 318 | ⚠️  Transpiles, C++ errors |

## Conclusion

✅ **Both requested bugs are FIXED**
✅ **Main function generation works correctly**
⚠️  **Full bootstrap blocked by other seed_cpp limitations** (not main() related)

The two bugs that prevented function bodies from generating are completely resolved. Further bootstrap progress requires addressing seed_cpp's handling of advanced language features.
