# S61: Interpreter Stack Overflow on app.io.mod Imports

**Status:** Open  
**Defect Type:** Interpreter module loader / missing cycle detection  
**Severity:** Critical (blocks direct imports of app.io.mod)  
**Affects:** BOTH deployed pure-Simple self-hosted binary (2026-07-11) AND Rust seed bootstrap  
**Root Cause:** Pure-Simple interpreter module loader lacks "is_currently_loading" tracking

## Symptom

Importing `use app.io.mod` directly causes stack overflow in both interpreter engines:

```bash
# Reproducer: direct import of app.io.mod
cat > /tmp/test_io_direct.spl <<'EOF'
use app.io.mod

describe "direct import":
    it "loads app.io.mod":
        expect(true).to_equal(true)
EOF

# BOTH binaries hang with timeout exit 143:
timeout 5 /home/ormastes/dev/wt_s9/bin/simple test /tmp/test_io_direct.spl  # Exit 143
timeout 5 /home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple test /tmp/test_io_direct.spl  # Exit 143
```

Tests that do NOT directly import app.io.mod complete successfully.

## Root Cause Analysis

### Pure-Simple Interpreter Module Loader Bug

The pure-Simple interpreter's module loader (src/compiler/10.frontend/core/interpreter/module_loader_core.spl) lacks **cycle detection during module load**.

**Flow that triggers the bug:**

1. `use app.io.mod` is processed
2. `load_module("app.io.mod", current_file)` is called (module_loader_core.spl:351)
3. Module is NOT yet marked as "loaded" — only depth tracking exists (line 366-368)
4. Source is parsed, AST is added to shared interpreter state
5. `extract_module_exports()` is called (line 395) — just scans AST
6. `register_module_functions()` is called (line 398) — just registers functions
7. Module is marked as loaded (line 401)
8. **BUT**: When eval_module() later processes declarations, it reaches Phase 1.5 (eval_decls.spl:196-201)
9. Phase 1.5 evaluates ALL DECL_USE statements immediately
10. If any use statement in app.io.mod (or its transitive deps) tries to re-load app.io.mod:
    - Check at line 356: `if module_is_loaded(module_name) == 1` → FALSE (module not YET marked as loaded)
    - Depth check at line 366: passes (depth is still low, only 16-level limit)
    - **Infinite recursion begins** → re-parse app.io.mod → re-process use statements → try to load app.io.mod again

### Missing "Currently Loading" Tracking

**Key Issue**: The loader only has ONE tracking structure: `loaded_module_set` (marked only AFTER full load).

**Missing**: A `currently_loading_set` to track modules still being loaded, which would catch cycles BEFORE they recurse.

Compare (Rust seed has this):
- Rust: `is_module_loading(&module_path)` at line 671 in module_loader.rs (detects in-flight modules)
- Pure-Simple: Only `module_is_loaded()` at line 356 (detects fully-loaded modules)

### Probable Re-entry Point

When app.io.mod is being evaluated:
- app.io.mod imports std.nogc_sync_mut.io.* files
- One of those files OR a transitive dependency might have a use statement that needs app.io module re-exports
- OR: eval_module's phase 1.5 evaluates ALL use statements, including those in app.io.mod itself, which haven't finished loading yet
- Those use statements call load_module() again for app.io.mod
- Since it's not yet marked as "loaded", the cycle recurses infinitely

## Files Involved

**Pure-Simple Interpreter (PRIMARY BUG)**:
- `src/compiler/10.frontend/core/interpreter/module_loader_core.spl`
  - `load_module()` (line 351): No "is_currently_loading" check before line 356
  - `module_is_loaded()` (line 163): Only checks `loaded_module_set`, not in-flight
  - Depth limit (line 366): Set to only 16 levels, insufficient for complex cycles
  - `module_mark_loaded()` (line 170): Called AFTER all processing
  
- `src/compiler/10.frontend/core/interpreter/eval_decls.spl`
  - Phase 1.5 (line 196-201): Evaluates all DECL_USE immediately
  - `eval_decl()` for DECL_USE (line 88): Calls load_module without pre-checking current stack

**Rust Seed (HAS PROPER DETECTION)**:
- `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs`
  - `is_module_loading()` check at line 671: Works correctly
  - Partial exports memoization: Handles cycles properly

## How to Fix

In src/compiler/10.frontend/core/interpreter/module_loader_core.spl:

1. Add a "currently_loading" tracking set (parallel to loaded_module_set)
2. At line 356, check BOTH:
   ```
   if module_is_loaded(module_name) == 1:
       return 1
   if module_is_currently_loading(module_name) == 1:
       return 1  # Return partial/empty dict to break cycle
   ```
3. Mark module as "loading" BEFORE parsing (line ~370)
4. Unmark from "loading" when fully loaded (line ~401)

## Test Case (Reproducer)

```bash
cd /home/ormastes/dev/wt_s9
cat > /tmp/test_io_direct.spl <<'EOF'
use app.io.mod
describe "test": it "x": expect(true).to_equal(true)
EOF

timeout 5 bin/simple test /tmp/test_io_direct.spl
# Expected: test completes with output
# Actual: times out (exit 143) with stack overflow
```

## Evidence

- Both binaries exhibit identical hang behavior on direct `use app.io.mod`
- Indirect use of app.io (through test framework) does NOT hang
- Depth limit (16 levels) is exceeded during recursive re-entry
- Rust seed has proper `is_module_loading()` detection; pure-Simple lacks it

## References

- Pure-Simple loader: src/compiler/10.frontend/core/interpreter/module_loader_core.spl:351-404
- Evaluation phases: src/compiler/10.frontend/core/interpreter/eval_decls.spl:196-201  
- Rust seed (working): src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:671-683

## STATUS: ROOT-CAUSE THEORY REFUTED (2026-07-17, S65 re-verification)

The module-import-cycle theory above does NOT survive independent re-verification
at origin tip 99f0294dbda against the deployed release binary:

1. `bin/simple run` on a file containing only `use app.io.mod` completes CLEAN
   (rc=0, normal output). Same for `use compiler.core.interpreter.module_loader_core`.
   Module loading is identical across entry commands, so a fatal load-time cycle
   in this graph cannot exist.
2. `bin/simple test` hangs (rc=124) on EVERY spec file — including a vanilla
   `describe/it` spec with zero `use` statements — wedging at the same point
   (after loading `std.nogc_sync_mut.test_runner.test_executor_composite_jit_generic`,
   zero further output between 90s and 240s). The hang is test-runner-init-wide,
   not app.io-specific. The repro in this doc reproduces the generic hang, not a
   module cycle.
3. The test-runner infra chain does not transitively import `app.io.mod` or
   `module_loader_core` (repo-wide grep negative).
4. The deployed release binary `bin/release/x86_64-unknown-linux-gnu/simple`
   (46,170,032 bytes, mtime 2026-07-11 08:52, sha256 prefix 561767c6615bc013) is
   a Rust SEED binary (prints the "bootstrap seed only" warning), not the
   self-hosted binary. Directory-mode `bin/simple test <dir>` additionally fails
   with `unknown extern function: rt_process_run_bounded` — that extern IS
   registered in current-tree seed source, so the stale binary predates it.

Superseding hypothesis: the single-file spec hang is the known stale-seed-binary
regression (see release-sanity finding "Jul-16 seed stage1 spin = seed-binary
regression (fresh seed clean)"), to be confirmed by running the vanilla-spec
probe on a freshly built seed. The loader-hardening change drafted from this
doc's theory (in-flight cycle tracking, lane S64) is held un-landed: plausible
defense-in-depth, but its motivating bug is unconfirmed and it is unverifiable
until redeploy.
