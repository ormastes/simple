# Interpreter Module Cleanup - Session 2026-02-03

## Summary

Fixed circular dependencies in the interpreter core module by:
1. Removing GLOBAL_INTERNER from public exports
2. Adding public API functions for symbol interning
3. Commenting out incomplete module dependencies (Lazy, PersistentDict)
4. Removing module caching feature that depended on incomplete types

## Changes Made

### 1. Symbol Module (src/app/interpreter/core/symbol.spl)

**Problem:** GLOBAL_INTERNER was exported before being defined, causing "Export statement references undefined symbol" warning.

**Solution:**
- Removed `export GLOBAL_INTERNER` statement entirely
- Added comment explaining it's internal-only
- Public API now provides `intern()`, `resolve()`, `get_or_none()` functions
- Clients should use these functions instead of direct GLOBAL_INTERNER access

**Benefits:**
- Eliminates circular dependency warnings
- Better API encapsulation
- Clearer separation between internal implementation and public interface

### 2. Environment Module (src/app/interpreter/core/environment.spl)

**Earlier fix (from previous session):**
- Replaced `from symbol import {GLOBAL_INTERNER}` with `from symbol import {get_or_none}`
- Updated all GLOBAL_INTERNER.get_or_none() calls to use get_or_none() function
- Replaced PersistentDict with Dict (PersistentDict not yet implemented)

### 3. Eval Module (src/app/interpreter/core/eval.spl)

**Problem:** Interpreter struct referenced incomplete types Lazy and PersistentDict.

**Solution:**
- Commented out imports: `from ..lazy import {Lazy}`, `from ..collections.persistent_dict import {PersistentDict}`
- Commented out `module_cache` field in Interpreter struct
- Removed module_cache initialization from `new()` and `with_debug()` constructors
- Commented out `get_or_load_module()` method entirely (not used anywhere)

**Code changes:**
```simple
# BEFORE:
struct Interpreter:
    env: Environment
    debug: bool
    module_cache: PersistentDict<text, Lazy<Value>>

# AFTER:
struct Interpreter:
    env: Environment
    debug: bool
    # TODO: Re-enable when Lazy and PersistentDict are complete
    # module_cache: PersistentDict<text, Lazy<Value>>
```

## Current Status

### Working
- FFI workspace: 100% complete (13 crates, 97+ FFI functions)
- Rust tests: 92/92 passing
- Symbol interning: Core functionality works
- Module loading: Basic structure loads without GLOBAL_INTERNER warnings
- Simple CLI: Can load and execute FFI-based code

### Issues Remaining
1. **Stack overflow in environment_spec.spl**: Module loading enters infinite loop with warning:
   ```
   Group import with empty path - skipping
   ```
   This suggests there's an import statement with empty path `[]` somewhere in the module chain.

2. **Test suite hangs**: Times out after 2 minutes, likely due to the same stack overflow issue.

3. **Incomplete modules still blocking tests**:
   - `collections` module (PersistentDict, PersistentVec)
   - `lazy` module (Lazy evaluation)
   - `async_runtime` module (actors, mailboxes)
   - `memory` module (RefcBinary)
   - `perf` module (performance tracking)

### Test Results
- **Before this session**: 24 Simple tests passing
- **After cleanup**: Unable to run full test suite due to stack overflow
- **Rust tests**: 92/92 passing (unaffected)

## Next Steps

### Immediate (P0 - Blocking)
1. **Find empty path import**: Search for the source of `load_and_merge_module{path=[]}` warning
   - Check eval.spl, environment.spl, symbol.spl for malformed imports
   - Check if commented imports are being partially parsed
   - Investigate module resolution logic in Rust compiler

2. **Fix stack overflow**: Once empty path import is found, fix or remove it

### Short-term (P1)
3. **Complete or mock incomplete modules**:
   - Either implement PersistentDict/Lazy properly
   - Or create minimal mock implementations that allow tests to run
   - Priority: PersistentDict (used in multiple places)

4. **Re-enable module caching**: Once Lazy and PersistentDict are complete
   - Uncomment module_cache field
   - Uncomment get_or_load_module method
   - Add tests for lazy module loading

### Medium-term (P2)
5. **Test interpreter integration**: Once basic tests pass
   - Environment variable binding tests
   - Symbol interning performance tests
   - Scope management tests

6. **Complete remaining interpreter modules**:
   - Collections (persistent data structures)
   - Async runtime (actors, scheduler)
   - Memory management (RefcBinary)

## Lessons Learned

1. **Circular dependencies in module systems are subtle**: Even a Display impl accessing a global variable can create issues during module loading.

2. **Commenting out incomplete features is effective**: Better to have a working subset than a broken superset.

3. **Public API functions > direct global access**: Using `intern()`, `resolve()`, `get_or_none()` is cleaner than exposing GLOBAL_INTERNER.

4. **Module loading traces are valuable**: The warning messages showing the exact load path helped identify the circular dependency chain.

## Files Modified

- `src/app/interpreter/core/symbol.spl`: Removed GLOBAL_INTERNER export, kept internal-only
- `src/app/interpreter/core/eval.spl`: Commented out Lazy/PersistentDict dependencies, removed module_cache
- `src/app/interpreter/core/environment.spl`: (Earlier) Replaced Dict for PersistentDict, use get_or_none()

## Verification

```bash
# Check Rust tests still pass
simple build rust test
# Output: 92/92 passing

# Check GLOBAL_INTERNER warning is gone
timeout 60 ./bin/simple test --no-rust-tests 2>&1 | grep GLOBAL_INTERNER
# Output: (none - warning eliminated)

# Check remaining issues
timeout 60 ./bin/simple test --no-rust-tests 2>&1 | grep -E "Group import|stack overflow"
# Output: "Group import with empty path - skipping" + stack overflow
```

## Completion Criteria

- [x] GLOBAL_INTERNER circular dependency fixed
- [x] Eval module cleaned of incomplete type references
- [x] Rust tests still passing (92/92)
- [ ] Stack overflow resolved (blocked on finding empty path import)
- [ ] Simple test suite runs without hanging
- [ ] Environment tests pass
