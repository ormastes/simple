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

## Fix Strategy

### Option 1: Debug Print Approach
Add comprehensive logging to trace where `hir_modules` gets lost.

### Option 2: Direct Mutation
Instead of:
```simple
var hir_modules = ctx.hir_modules
hir_modules[name] = resolved_module
ctx.hir_modules = hir_modules
```

Try:
```simple
# Direct mutation (if supported)
ctx.hir_modules[name] = resolved_module
```

### Option 3: Accumulator Pattern
Build a new context with accumulated HIR modules:
```simple
var new_hir_modules = ctx.hir_modules
for name in module_names:
    ...
    new_hir_modules = new_hir_modules.with(name, resolved_module)
ctx = ctx.with_hir_modules(new_hir_modules)
```

## Success Criteria

- Bootstrap succeeds: `simple_new1` can compile itself to produce `simple_new2`
- `[aot] MIR done, N modules` shows correct count (N ≥ 1)
- All unit tests pass after fix

## Notes

- This bug affects **generation 2** of bootstrap, not generation 1
- `simple_old` (Rust implementation) successfully compiles to `simple_new1`
- Bug is in the **Simple-based compiler implementation**, not Rust runtime
- MCP server integration planned to help analyze this and future bugs
