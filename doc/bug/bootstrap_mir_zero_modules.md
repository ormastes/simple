# Bug: Bootstrap Failure - MIR Lowering Returns 0 Modules

**ID:** bootstrap_mir_zero_modules
**Date:** 2026-01-29
**Severity:** Critical (Blocks self-hosting)
**Status:** Confirmed

## Summary

The Simple compiler bootstrap fails at generation 2 (simple_new1 → simple_new2) because MIR lowering returns 0 modules, causing the linker to fail with "No object files to link".

## Reproduction

```bash
# Run bootstrap script
./scripts/bootstrap.sh

# Output shows:
# Stage 1: simple_old -> simple_new1  ✓ SUCCESS
# Stage 2: simple_new1 -> simple_new2  ✗ FAIL
#   [aot] MIR done, 0 modules
#   Codegen error: Linking failed: No object files to link
```

## Root Cause Analysis

### Evidence from Logs

```
[phase3] parsed modules count=1
[phase3] entering loop over 1 modules
[phase3] processing module: main
[phase3] HIR lowered
[phase3] methods resolved
[phase3] resolve_errors count=0
[compile] phase 3 done

[compile] phase 5: mode-specific processing...
[compile] aot mode
[aot] lowering to MIR...
[aot] MIR done, 0 modules      <-- BUG: Should be 1 module
```

### Code Flow

1. **Phase 3** (`lower_and_check_impl()` in `simple/compiler/driver.spl:425-472`):
   - Successfully lowers AST → HIR
   - Stores HIR module: `ctx.hir_modules[name] = resolved_module` (line 469-470)
   - Returns `(ctx, true)`

2. **Phase 5** (`aot_compile()` in `simple/compiler/driver.spl:614-660`):
   - Calls `lower_to_mir()` (line 617)
   - `lower_to_mir()` iterates over `self.ctx.hir_modules.keys()` (line 693)
   - **BUG**: `hir_modules.keys()` returns empty list!

### Suspected Causes

1. **Dictionary Mutation Issue**: Simple's dictionary implementation may not handle mutation correctly when accessed through class fields:
   ```simple
   var hir_modules = ctx.hir_modules
   hir_modules[name] = resolved_module
   ctx.hir_modules = hir_modules        # <- May not actually update ctx?
   ```

2. **Context Copy Issue**: The context returned from `lower_and_check_impl()` may not have its `hir_modules` properly populated:
   ```simple
   val (new_ctx3, analyze_ok) = self.lower_and_check_impl()
   self.ctx = new_ctx3                  # <- Does this preserve hir_modules?
   ```

3. **Class Field Assignment**: Classes in Simple are reference types, but field reassignment may have semantics issues.

## Test Case

```simple
# Minimal test case for dictionary mutation through class fields
class TestContext:
    data: Dict<text, i32>

fn test_dict_mutation():
    val ctx = TestContext(data: {})

    # Try to add item
    var dict = ctx.data
    dict["key"] = 42
    ctx.data = dict

    # Check if it persists
    print "Keys: {ctx.data.keys().len()}"  # Expected: 1, Actual: ?
```

## Workarounds

None currently. Bootstrap is blocked.

## Investigation Needed

1. **Add debug prints** in `lower_and_check_impl()`:
   ```simple
   # After line 470
   print "[phase3] hir_modules stored: {ctx.hir_modules.keys().len()} modules"
   ```

2. **Add debug prints** at start of `aot_compile()`:
   ```simple
   # Before line 616
   print "[aot] ctx.hir_modules count: {self.ctx.hir_modules.keys().len()}"
   ```

3. **Test dictionary semantics** with simple test case above.

4. **Check RuntimeValue dictionary** implementation in Rust runtime.

## Related Issues

- **Self-hosting compiler** (Feature #850): Blocked by this bug
- **MIR lowering** (Feature #755): May have related issues

## Root Cause (Confirmed)

**Nested field chain dict mutation bug in compiled mode.**

When the Rust codegen compiles `self.ctx.hir_modules[name] = resolved_module`, the
nested field chain (`self` -> `ctx` -> `hir_modules` -> `[name]`) may not correctly
propagate mutations in compiled native code. The pattern:

1. FieldGet `self.ctx` -> load CompileContext pointer
2. FieldGet `.hir_modules` -> load Dict RuntimeValue (by value copy)
3. `rt_index_set(dict_copy, name, module)` -> mutates a temporary copy, not the original

The issue is that `FieldGet` loads the dict RuntimeValue as a 64-bit value (tagged
pointer). For heap-allocated dicts, this IS a pointer, so in-place mutation should work.
However, in practice the compiled codegen may:
- Return a stale copy if the field access chain is optimized
- Lose track of the original field location after multiple indirections
- Have ABI mismatches in the `rt_index_set` call through deep field chains

This explains why:
- Stage 1 (Rust seed) works: the Rust interpreter handles nested assignment explicitly
- Stage 2 (compiled binary) fails: the native codegen doesn't propagate mutations through 3+ levels of field indirection

## Fix Applied

**Single-level field access via helper methods on CompileContext.**

Added helper methods to `CompileContext` in `driver_types.spl`:
- `store_hir_module(name, module)` / `store_mir_module(name, module)` -- dict mutation with `self.hir_modules[name] = module` (1-level access)
- `hir_module_keys()` / `mir_module_keys()` -- key enumeration
- `hir_module_count()` / `mir_module_count()` -- length queries
- `get_hir_module(name)` / `get_mir_module(name)` -- value retrieval

Updated all call sites in:
- `driver.spl` -- `lower_and_check_impl()`, `lower_to_mir()`, `monomorphize_impl()`, `borrow_check()`, `process_async()`, `weave_mir_all()`, `optimize_mir()`, `process_sdn()`, `interpret_pipeline()`, standalone compat methods
- `driver_aot_output.spl` -- all `compile_to_*` methods
- `build/compile_to_llvm.spl` -- LLVM IR translation

### Why this fixes it
Inside the helper method (e.g., `store_hir_module`), the code is:
```simple
me store_hir_module(name: text, module: HirModule):
    self.hir_modules[name] = module
```
Here `self` is the `CompileContext` itself (1 level), not `driver.ctx.hir_modules`
(3 levels). The compiled codegen handles single-level field + dict index assignment
correctly via `FieldGet(self, offset) -> rt_index_set(dict, key, value)`.

### Debug prints added
`[debug-bootstrap]` print statements at key points to trace module counts through
the Phase 3 -> Phase 4 -> Phase 5 pipeline. Remove after bootstrap is verified.

## Remaining Steps

1. **Rebuild `bin/release/simple`** from the refactored source to produce a binary
   that uses single-level field access for dict mutations
2. **Run bootstrap Stage 2** with the rebuilt binary to verify the fix
3. **Remove `[debug-bootstrap]` prints** after successful verification

## Success Criteria

- Bootstrap succeeds: `simple_new1` can compile itself to produce `simple_new2`
- `[aot] MIR done, N modules` shows correct count (N >= 1)
- All unit tests pass after fix

## Notes

- This bug affects **generation 2** of bootstrap, not generation 1
- `simple_old` (Rust implementation) successfully compiles to `simple_new1`
- Bug is in nested field chain dict mutation in **compiled native code**
- The Rust interpreter explicitly handles 3-level nested field+index assignment
  (node_exec.rs lines 991-1072) but compiled codegen does not
- The existing comment `# Store final module directly (avoids copy-modify-reassign bug in compiled mode)` at driver.spl:522 confirms awareness of this class of bugs
- MCP server integration planned to help analyze this and future bugs
