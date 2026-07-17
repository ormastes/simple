# S61: Interpreter Stack Overflow on app.io.mod Imports

**Status:** Open  
**Defect Type:** Interpreter module loader / cycle detection  
**Severity:** Critical (blocks all app.io tests)  
**Evidence:** `bin/simple test test/01_unit/app/io/io_numeric_guard_spec.spl` times out on stack overflow after ~2 minutes  

## Symptom

Running any test that exercises app.io modules causes the interpreter to hang and stack overflow:

```bash
# Hangs with stack overflow
timeout 10 bin/simple test test/01_unit/app/io/io_numeric_guard_spec.spl
```

All app.io tests in `test/01_unit/app/io/` are blocked.

## Root Cause Analysis

The issue is a **defect in the Rust seed interpreter's module loader** (src/compiler_rust/compiler/src/interpreter_module/module_loader.rs).

### Import Redirect Cycle

When importing from app.io, the module loader redirects group/glob imports to __init__.spl:

1. **Import Path Redirect**: `prefer_package_init_for_member_import()` (line 377-392 in module_loader.rs)
   - Redirects: `use app.io.mod (item)` → loads `src/app/io/__init__.spl` instead of `src/app/io/mod.spl`
   - Trigger: Group or Glob imports only (lines 379-380)

2. **__init__.spl Structure** (src/app/io/__init__.spl):
   - Line 6-15: Bare `mod` declarations (not real imports)
   - Line 58: `export use app.io.mod.{ ... many items ... }`
   - This export-use triggers loading of app/io/mod.spl

3. **Problematic Sequence**:
   - Test tries: `use app.io (any_item)` or test framework itself loads app.io
   - Loader redirects to app/io/__init__.spl and marks it as "loading"
   - __init__.spl evaluation processes: `export use app.io.mod`
   - This calls `load_and_merge_module()` for app.io.mod
   - app.io.mod.spl imports from std.nogc_sync_mut.io.* (line 16-92)
   - **Unknown link**: One of these modules or sibling preloading re-tries to load a module that's already marked as loading
   - Cycle detection returns partial exports (lines 671-683 in module_loader.rs)
   - But evaluation continues re-recursing somewhere without properly checking the loaded flag

### Suspected Code Path

1. Line 881-896 in module_loader.rs: **Sibling preloading** during __init__.spl evaluation
   - Collects all .spl files in app/io directory (siblings of __init__.spl)
   - Calls `evaluate_module_exports()` for each sibling
   - **Bug candidate**: A sibling's evaluate_module_exports triggers a re-import of a module still being loaded, but the cycle detection isn't applied uniformly

2. Alternative: The `mod` declarations (lines 6-15 in __init__.spl) might be interpreted as implicit imports by the evaluation layer, causing hidden re-entrance.

## Files Involved

- **Rust Interpreter Module Loader**: `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs`
  - `load_and_merge_module()` function (line 455)
  - Cycle detection (line 671-683): `if is_module_loading(&module_path)`
  - Sibling preloading (line 754-926)
  
- **Module Evaluator**: `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`
  - `process_use_stmt()` (line 482): Calls load_and_merge_module
  
- **Affected Modules**:
  - `src/app/io/__init__.spl` (line 58): export use app.io.mod
  - `src/app/io/mod.spl` (line 16-92): Multiple std.nogc_sync_mut.io imports
  - `src/app/io/process_env_ops.spl`: Re-imported on line 33 of mod.spl

## Hypothesis

The cycle detection works for direct A→B→A cycles, but fails when:
1. Module A is marked as "loading"
2. During A's evaluation, sibling module B is preloaded
3. B's evaluation indirectly triggers re-loading of a module C
4. C (or a module it loads) transitively depends on A
5. The cycle is detected (returning partial exports), but **the stack doesn't unwind** — control returns to sibling preloading loop, which continues calling evaluate_module_exports on more siblings
6. Eventually, a sibling's evaluation hits the same cycle again, but evaluation context keeps growing

**Key Issue**: The cycle detection returns early (line 676-677), but the parent evaluation context continues with partial data, and re-entrance happens without proper depth reset or memoization.

## Required Fix

This is a **seed Rust interpreter bug**, not a .spl module structure problem. Possible fixes:

1. **Prevent sibling preloading recursion**: Skip sibling preloading if any module in the current call stack is already being loaded
2. **Improve memoization**: Cache the partial-exports result more aggressively so re-entrance always hits the cache
3. **Depth-aware cycle detection**: Track not just which module is loading, but whether we're in a sibling preload context, and avoid recursing into heavy evaluation

## Workaround

None available for the interpreter. The pure-Simple compiler (not yet available/deployed) should not have this issue.

## Test Case

```bash
# Minimal repro
cd /home/ormastes/dev/wt_s9
timeout 5 bin/simple test test/01_unit/app/io/io_numeric_guard_spec.spl
# Expected: test runs and completes
# Actual: times out with stack overflow
```

## References

- Module loader cycle detection: src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:671-683
- Sibling preloading logic: src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:754-926
- Affected module structure: src/app/io/__init__.spl and src/app/io/mod.spl
