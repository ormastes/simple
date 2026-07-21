# Bug: ModuleLoader load/unload bookkeeping diverges from documented behavior (13 failures)

- **Status:** open
- **Filed:** 2026-07-20
- **Affected spec:** `test/unit/compiler/loader/module_loader_spec.spl`
- **Command:**
  `SIMPLE_RUST_SEED_WARNING=0 timeout 25 bin/release/x86_64-unknown-linux-gnu/simple test test/unit/compiler/loader/module_loader_spec.spl --no-session-daemon`
- **Result:** `22 examples, 13 failures` (9 pass)

## Symptom (representative failures)

```
✗ loads an existing path and tracks it as loaded
    expected 0 to equal 1
✗ loads a module with a symbol and resolves it from globals
    expected call result to be truthy, got 0
✗ loads multiple existing paths and reports module count
    expected 0 to equal 2
✗ unloads modules and drops their JIT-owned symbols
    expected stale to equal hot_reload_fn
✗ unloads metadata-owned jit symbols even after owner drifted to __jit__
    expected stale to equal Vec$i64
✗ unload removes owned globals, clears metadata-owned jit symbols, preserves
  unrelated globals, and clears loaded metadata
    expected true to equal false
✗ impl-method unload clears modules entry for the path
    expected call result to be truthy, got false
✗ impl-method unload drops global symbols owned by that module
    expected true to equal false
✗ impl-method unload clears loaded_metadata for the path
    expected true to equal false
✗ impl-method unload clears jit_cache entries for symbols of the module
    expected true to equal false
✗ impl-method double-unload is idempotent: second call is a no-op
    expected true to equal false
✗ impl-method unload after JIT symbols are registered removes them correctly
    expected still_present to equal jit_owned_fn
✗ reload rehydrates on-disk metadata so persisted jit symbols stay resolvable
    expected missing to equal Vec$i64
```

Passing (9): default-config creation, "returns error for nonexistent path",
"loads modules and reports resolved symbol count", JIT-backed symbol
resolution, generic mangling/resolution, "preserves global symbols owned by a
different module", "no-op unload of never-loaded path", "identical
module-table state across loaders".

## Root cause (hypothesis, not confirmed — no src edit attempted)

The first failing case is the clearest signal:

```
var loader = ModuleLoader.with_defaults()
val result = loader.load(existing_module_path())
match result:
    case LoadResult.Success(module):        # <- this arm is taken (no "unexpected" failure)
        expect(module.path).to_equal(path)  # <- passes
    case _:
        expect("unexpected").to_equal(path)

expect(loader.is_loaded(path)).to_equal(true)          # passes
expect(loader.loaded_modules().len()).to_equal(1)      # not shown as failing individually,
expect(loader.stats().module_count).to_equal(1)        # FAILS: "expected 0 to equal 1"
```

`loader.load(path)` returns `LoadResult.Success` (the match succeeds and
`module.path` is correct), yet `loader.stats().module_count` reports `0`
instead of `1` afterward. This points to `ModuleLoader.stats()` (or the
counter it reads) not being updated by the same code path that `load()` uses
under the SSpec test evaluator — the module is loaded and resolvable
(`is_loaded` returns true) but the aggregate stats/module-count bookkeeping is
stale. The unload-family failures (`impl-method unload clears modules entry`,
`clears jit_cache entries`, `double-unload is idempotent`, etc.) show the same
shape: booleans/counts that should reflect post-unload state are reporting the
pre-unload (or default/zero) state instead.

This could be the same class of divergence as the documented `bin/simple test`
vs `bin/simple run` evaluator gap (see
`generic_class_static_method_unresolved_under_test_2026-07-20.md` /
`enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20.md`), but
the error signature here is different (clean value mismatches, not "unknown
static method"/"variable not found"), so it is filed separately rather than
folded into those docs. Root-causing requires stepping through
`src/compiler/99.loader/module_loader.spl` `load()`/`unload()`/`stats()` under
the test evaluator specifically, which is out of scope for this triage pass
(no Rust seed source fix attempted; src/** not touched).

## Repro (trimmed)

```
use compiler.loader.module_loader.*
var loader = ModuleLoader.with_defaults()
val result = loader.load("test/unit/compiler/loader/module_loader_spec.spl")
# result matches LoadResult.Success(module) with correct module.path
print(loader.stats().module_count)   # prints 0, expected 1
```

Not touched: `test/unit/compiler/loader/module_loader_spec.spl` left as-is —
these are genuine state-tracking mismatches, not renamed/removed API surface;
weakening the assertions to force green would violate the no-weakening rule.
