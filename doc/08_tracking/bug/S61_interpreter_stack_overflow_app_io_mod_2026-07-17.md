# S61: Interpreter Stack Overflow on app.io.mod Imports

**Status:** Closed — non-reproducing, verify-already-fixed (2026-07-18, see STATUS UPDATE below)  
**Defect Type:** Interpreter module loader / missing cycle detection (theory refuted)  
**Severity:** Was Critical; downgraded — symptom does not reproduce  
**Affects:** Originally claimed BOTH deployed pure-Simple self-hosted binary (2026-07-11) AND Rust seed bootstrap; neither reproduces on independent re-verification  
**Root Cause:** Theorized: pure-Simple interpreter module loader lacks "is_currently_loading" tracking. Refuted twice (2026-07-17, 2026-07-18); real crash this doc was chasing had a different, already-fixed root cause (see sibling doc referenced below).

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

## STATUS UPDATE 2026-07-18 (Lane C2): symptom confirmed non-reproducing; closing

Independently re-verified from scratch (fresh worktree, fresh seed binaries
dated 2026-07-18, both `bin/release/x86_64-unknown-linux-gnu/simple` and
`src/compiler_rust/target/bootstrap/simple` — neither is the stale 07-11
binary flagged above). All available binaries in this environment self-report
as the Rust bootstrap seed (`--version` prints the "bootstrap seed only"
warning); no self-hosted (pure-Simple) binary exists anywhere on this machine.

1. **Exact repro from this doc, re-run clean.** `bin/simple run` on a file
   containing only `use app.io.mod` completes with output and exit 0 (no
   stack overflow). The same file wrapped as a `describe`/`it` BDD spec, run
   via `bin/simple run <file>` (not `test`), reports `1 example, 0 failures`,
   exit 0. Both are now locked in as a permanent regression spec:
   `test/03_system/infrastructure/app_io_mod_direct_import_no_stack_overflow_spec.spl`
   (run via `bin/simple run <spec>`, not `bin/simple test <spec>` — see below).
2. **`bin/simple test` still hangs, but identically for a zero-`use` spec.**
   Re-confirms point 2 of the 2026-07-17 refutation above: `timeout 20 bin/simple
   test <spec-with-use-app.io.mod>` and `timeout 20 bin/simple test
   <spec-with-use-app.io.mod> --no-session-daemon` both time out (rc=124/143),
   wedging after loading `test_executor_composite_jit_generic` — the same
   test-runner-init-wide hang, unrelated to app.io.mod. This is a separate,
   already-tracked, out-of-scope regression (not module-loader cycle related).
3. **Synthetic mutual-import cycle also does not hang/crash.** A minimal
   two-file fixture (`mod_a.spl` uses `.mod_b.{b_val}`, `mod_b.spl` uses
   `.mod_a.{a_val}`, a `main.spl` uses both) run via `bin/simple run` completes
   cleanly (`a=1 b=2`, exit 0) — a genuine circular `use` does not stack
   overflow under the interpreter actually available in this environment.
   This corroborates the sibling doc's finding
   (`doc/08_tracking/bug/interp_app_io_mod_import_stack_overflow_2026-07-17.md`)
   that `module_cache.rs`/`module_evaluator.rs` (Rust seed) already have
   correct circular-import detection.
4. **Code audit of `module_loader_core.spl` found no depth-guard bypass.**
   All three public entry points (`load_module`, `load_module_register_only`,
   `load_module_parse_only`) check `_module_load_depth >= _MODULE_LOAD_MAX_DEPTH`
   (16) before any parse/recurse work and decrement it on every exit path
   (success and failure). The only caller of these from `DECL_USE` evaluation
   (`eval_decls.spl`'s `eval_decl`/Phase 1.5) routes exclusively through these
   guarded entry points — no path was found that re-enters module loading
   without passing through the depth counter. A cycle would exhaust the depth
   guard and fail to load (return 0), not overflow the native stack.
5. **The pure-Simple loader code path is unexercisable here, confirmed two
   ways.** (a) Every binary on this machine self-identifies as the Rust seed;
   `module_loader_core.spl` only executes under a self-hosted binary, which
   does not exist as a built artifact anywhere accessible. (b) Attempting to
   probe the file indirectly — a driver script doing
   `use compiler.core.interpreter.module_loader_core.{totally_nonexistent_fn}`
   — did not even raise a resolution error under the seed (the seed's `use`
   resolution for this compiler-internal namespace is a no-op from ordinary
   scripts and does not validate referenced symbols), so no meaningful syntax
   or behavior probe of this file is possible without a redeploy. This
   matches and reconfirms the "unverifiable until redeploy" conclusion above;
   the S64-drafted `is_currently_loading` guard was NOT landed in this pass
   for the same reason — landing an unverifiable change to a hot interpreter
   path for a bug with no live repro would be exactly the kind of
   over-engineering the repo's coding rules warn against. The draft remains
   available in history for whoever picks this up once a self-hosted binary
   is available to verify it against.

**Conclusion:** S61's original root-cause theory (module loader lacks cycle
detection) does not hold up under two independent re-verification passes
(2026-07-17 and 2026-07-18) using different binaries/environments. The actual
`app.io.mod` stack-overflow crash that motivated this investigation was a
different, already-fixed bug (see
`doc/08_tracking/bug/interp_app_io_mod_import_stack_overflow_2026-07-17.md`:
`fs_helpers.spl` self-shadowing import + `STACK_OVERFLOW_DETECTION_ENABLED`
defaulting off in release, both fixed). Recommend closing this doc as
verify-already-fixed / non-reproducing, cross-referenced to the sibling
resolved doc, with the regression spec above as the permanent guard.
