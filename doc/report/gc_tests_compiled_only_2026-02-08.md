# GC Tests - Compiled-Only Analysis - 2026-02-08

**Goal:** Write real test implementations for 102 GC tests (currently stubbed with `check(true)`)
**Result:** ❌ **IMPOSSIBLE** - GC module is compiled-only, cannot run in interpreter
**Status:** Task completed (determined not feasible)

## Summary

Attempted to convert 102 stubbed GC tests from `skip_it` placeholders to real test implementations. Discovered that the `std.gc` module **cannot be parsed by the runtime parser** due to use of generics, making all GC tests compiled-only.

## Investigation

### Parse Error

When attempting to import `std.gc` in test file:

```
ERROR: Failed to parse module path="./src/std/gc.spl"
error=Unexpected token: expected identifier, found Lt
```

**Cause:** The runtime parser encounters `GcPtr<T>` and fails on the `<` character (Lt = "less than"). Generics are not supported in the runtime parser.

### Why GC Module is Compiled-Only

The `src/std/gc.spl` module uses multiple features not available in the interpreter:

1. **Generics**: `class GcPtr<T>:` - runtime parser doesn't support `<>` syntax
2. **Allocator types**: `ArenaAllocator`, `SlabAllocator` - from `std.allocator`
3. **Runtime internals**: `RuntimeValue`, `AtomicBool` - from `std.runtime_value`, `std.atomic`
4. **FFI functions**:
   - `extern fn header_size() -> usize`
   - `extern fn write_header(ptr: [u8], header: GcObjectHeader)`
   - `extern fn read_header(ptr: [u8]) -> GcObjectHeader`
   - `extern fn write_header_field(ptr: [u8], field: text, value: [u8]?)`
   - `extern fn type_id_of<T>() -> i32`
   - `extern fn ptr_add(ptr: [u8], offset: usize) -> [u8]`
   - `extern fn ptr_sub(ptr: [u8], offset: usize) -> [u8]`
   - `extern fn read_i64(ptr: [u8]) -> i64`
   - `extern fn current_time_micros() -> i64`

All of these features require the JIT compiler to work.

### Test Status

```
✅ Correctly marked as compiled-only in test runner
✅ All 102 tests have skip_it placeholders
✅ Test file documents why tests are skipped
```

## Attempted Approach

1. Created helper functions to work around static methods:
   - `fn gc_object_header(size, type_id) -> GcObjectHeader`
   - `fn gc_config_default() -> GcConfig`
   - `fn gc_stats_new() -> GcStats`

2. Converted first 14 tests (GcObjectHeader, GcConfig, GcStats) from `skip_it` to `it`

3. Ran tests and discovered parse error preventing module load

4. Reverted all changes - tests must remain `skip_it`

## Test Breakdown

Total: 102 tests (all compiled-only)

| Category | Count | Reason |
|----------|-------|--------|
| GcObjectHeader | 7 | Requires module import |
| GcConfig | 3 | Requires module import |
| GcStats | 4 | Requires module import |
| GcHeap - Basic | 7 | Uses allocators + FFI |
| GcHeap - Roots | 3 | Uses allocators + FFI |
| GcHeap - Collection | 6 | Uses allocators + FFI |
| GcHeap - Mark Phase | 2 | Uses allocators + FFI |
| GcHeap - Sweep Phase | 2 | Uses allocators + FFI |
| GcPtr | 4 | Uses generics |
| Integration | 5 | Full GC functionality |
| Use Cases | 2 | Full GC functionality |
| Tri-Color Marking | 6 | GC internals |
| Generational | 6 | GC internals |
| Mark Phase Edges | 6 | GC internals |
| Sweep Phase Edges | 5 | GC internals |
| Finalization | 5 | GC internals |
| Memory Pressure | 6 | GC internals |
| GC Statistics | 9 | GC internals |
| Object Sizes | 5 | Allocation |
| Incremental GC | 3 | GC internals |
| Concurrent GC | 2 | GC internals |
| Stress Tests | 4 | Full GC functionality |

## Conclusion

**GC tests are correctly marked as compiled-only.** They cannot be converted to interpreter-runnable tests because:

1. The module itself uses generics which the runtime parser doesn't support
2. Even if generics were removed, the module depends on FFI functions and runtime internals
3. The GC is a low-level system component that fundamentally requires compiled code

**Recommendation:** Keep all 102 tests as `skip_it` placeholders. They will run when the JIT compiler is fully implemented. Do not attempt to make them interpreter-runnable.

## Files Examined

- `src/std/gc.spl` (649 lines) - GC implementation
- `test/lib/std/unit/gc_spec.spl` (426 lines) - Test suite

## Next Steps

Since GC tests are compiled-only, the next priority should be:

1. ✅ **MCP error handler** - Fix parse error blocking 34 tests (90% complete)
2. ⏭️  **Debug library** - Check if debug tests can be implemented (104 tests)
3. ⏭️  **Other skipped tests** - Find interpreter-runnable tests to enable

---

**Time Spent:** 1 hour (investigation + attempted implementation + documentation)
**Tests Enabled:** 0 (not possible)
**Key Learning:** Runtime parser limitation with generics prevents testing of generic types
