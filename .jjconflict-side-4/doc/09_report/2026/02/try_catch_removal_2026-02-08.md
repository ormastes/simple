# try/catch/throw Removal - Complete

**Date:** 2026-02-08
**Task:** Remove all try/catch/throw usage from codebase (not supported in Simple)

## Summary

✅ **All try/catch blocks removed from src/ code**
✅ **Test files already had try/catch commented out**
✅ **Documentation comments explaining "not supported" kept**

## Changes Made

### 1. src/lib/pure/tensor_ops_hybrid.spl (5 functions fixed)

**Removed try/catch fallback pattern:**
```simple
# ❌ BEFORE (not supported)
if should_use_ffi("op", numel):
    try:
        return op_torch_ffi(a, b)
    catch:
        return op_pure(a, b)
else:
    return op_pure(a, b)

# ✅ AFTER (Simple-compatible)
if should_use_ffi("op", numel):
    return op_torch_ffi(a, b)
else:
    return op_pure(a, b)
```

**Functions updated:**
- `add()` - Element-wise addition
- `sub()` - Element-wise subtraction
- `mul()` - Element-wise multiplication
- `matmul()` - Matrix multiplication
- `relu()` - ReLU activation

**Added note:** "NOTE: try/catch not supported - FFI wrappers must handle errors internally."

## Files Checked (No Changes Needed)

### Test Files (already commented out)
- `test/compiler/blocks/builder_api_spec.spl` - Line 31-35 already commented
- `test/lib/std/unit/testing/benchmark_spec.spl` - Line 204-208 already commented
- `test/lib/std/unit/testing/mock_spec.spl` - Line 508-512 already commented

### Documentation (kept - explains limitation)
- `src/lib/spec.spl:17` - "NOTE: No static fn, no try/catch/throw"
- `src/app/desugar/rewriter.spl:21` - "NOTE: No try/catch/throw - Simple does not support exceptions"

### Bug Comments (kept - explains workaround)
- `src/lib/database/test_extended.spl` - 14 instances of "BUG-044: Use ?? instead of ? to avoid 'try: early return'"

### Type System (kept - part of effect system)
- `src/compiler/hir_types.spl:562` - `Throws(type_: HirType)` enum variant (effect system design)

### Other Comments (kept - documentation)
- `src/lib/src/testing/gpu_helpers.spl:58` - Comment about SkipException
- `src/app/interpreter/extern/file_io.spl:358` - Result type documentation
- `src/compiler/backend/cuda/ptx_builder.spl:61` - String interpolation, not exception

## Verification

```bash
# No uncommented try/catch/throw in src/
$ grep -rn "^\s*try:" src/ --include="*.spl" | grep -v "#"
# (no output)

$ grep -rn "^\s*catch:" src/ --include="*.spl" | grep -v "#"
# (no output)

$ grep -rn "^\s*throw " src/ --include="*.spl" | grep -v "#"
# (no output)
```

## Impact

**Before:** 5 try/catch blocks in production code (parsing would fail)
**After:** 0 try/catch blocks in production code

**Line reduction:** 232 lines (from ~247 with try/catch blocks)

**Benefit:**
- Code now follows documented language limitation
- FFI wrappers simplified (direct calls, no exception handling)
- Consistent with MEMORY.md: "NO EXCEPTIONS: try/catch/throw NOT supported"
- File parses correctly in runtime interpreter

## Next Steps

If error handling needed in FFI wrappers:
1. Use Option/Result return types
2. Use `??` null coalescing operator
3. Return error values explicitly
4. Document error conditions in comments

Example:
```simple
fn add_torch_ffi(a: PureTensor<f64>, b: PureTensor<f64>) -> PureTensor<f64>:
    # If FFI fails, return fallback to pure implementation
    # FFI stub currently just calls pure version
    add_pure(a, b)
```

## Error Handling Patterns in Simple

Since try/catch is not supported, use these patterns:

### Pattern 1: Option Types
```simple
fn safe_divide(a: f64, b: f64) -> f64?:
    if b == 0.0:
        return nil
    return a / b

val result = safe_divide(10.0, 2.0) ?? 0.0  # Default to 0.0 if nil
```

### Pattern 2: Result Types (when available)
```simple
enum Result<T, E>:
    Ok(value: T)
    Err(error: E)

fn parse_int(s: text) -> Result<i64, text>:
    # ... parsing logic
    if valid:
        return Result.Ok(parsed_value)
    else:
        return Result.Err("Invalid format")
```

### Pattern 3: Error Return Values
```simple
fn process() -> text:  # Returns "" on success, error message on failure
    if error_condition:
        return "Error: something went wrong"
    return ""  # Success

val error = process()
if error != "":
    print "Failed: {error}"
```

## Files Modified

- `src/lib/pure/tensor_ops_hybrid.spl` (5 functions updated, 15 lines removed)

## Conclusion

All try/catch/throw usage has been removed from production code. The codebase is now consistent with the documented language limitation (MEMORY.md: "NO EXCEPTIONS: try/catch/throw NOT supported").

Test files already had try/catch properly commented out with explanatory notes. Documentation comments explaining the limitation were preserved.
