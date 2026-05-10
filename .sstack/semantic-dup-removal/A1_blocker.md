# A1 Blocker: me unload delegation fails in interpreter — field reassignment not propagated

**Date:** 2026-04-28
**Phase:** 5 (implement)
**Cluster:** A1

---

## Summary

The A1 refactor (reduce `me unload` 38-line body to a one-line delegator calling `moduleloader_unload`) is blocked by a Simple interpreter semantics limitation: field reassignments made inside a `me` free function do NOT propagate back to the caller's `self` when called from within an `impl me` block.

Both delegation forms were tested and both fail:

1. `moduleloader_unload(self, path)` — free-function call, passes self by value in impl context
2. `self.moduleloader_unload(path)` — dot-dispatch form, same result

**The original 38-line body passes all 22 tests. Either delegation form fails 6 tests.**

---

## Evidence

### Passing baseline (original body)
```
22 examples, 0 failures
PASSED (101ms)
```

### Failing delegator forms (both tried)
```
22 examples, 6 failures
FAILED (100ms)

✗ impl-method unload clears modules entry for the path
  expected true to equal false
✗ impl-method unload drops global symbols owned by that module
  expected true to equal false
✗ impl-method unload clears loaded_metadata for the path
  expected true to equal false
✗ impl-method unload clears jit_cache entries for symbols of the module
  expected true to equal false
✗ impl-method double-unload is idempotent: second call is a no-op
  expected true to equal false
✗ impl-method unload and free-function unload produce identical module-table state
  expected 1 to equal 0
```

---

## Root Cause

`moduleloader_unload` performs field reassignment on `self`:
```simple
self.modules = self.modules.remove(path)
self.global_symbols = rebuilt_globals
self.jit.loaded_metadata = loaded_metadata_remove_path(...)
```

When `me unload` (an impl method) delegates to this free function, the interpreter does not propagate these field reassignments back into the caller's struct. This is distinct from in-place dict-index mutations (`self.modules[path] = m`) which do propagate — which is why the analogous `me load → moduleloader_load` delegation works correctly (load only uses in-place dict inserts).

This is not a code logic divergence between the two bodies — the bodies are character-for-character equivalent as confirmed by visual diff. The blocker is a Simple interpreter semantics issue.

---

## Contrast: Why `me load` delegation works

`moduleloader_load` only does `self.modules[path] = m` (in-place dict mutation via index operator). This likely works via reference semantics on the dict. No full field reassignment (`self.X = new_value`) occurs. That's why the A1 research and arch.md said "follow the load pattern" — but the load pattern is coincidentally safe; unload is not.

---

## Relevant test file

`test/unit/compiler/loader/module_loader_spec.spl` — lines 353–534 (Phase 4 A1 it-blocks)

---

## State of the source file

`src/compiler/99.loader/module_loader.spl` was restored to HEAD (git-tracked original 38-line body). No net change was made. The file is clean.

---

## Options for resolution (not A1's responsibility to implement)

1. **Compiler fix:** Fix the Simple interpreter to propagate field reassignments from `me` free function calls through impl-method delegations. This is the correct long-term fix. After the fix lands, A1 can be retried with either delegation form.

2. **Alternative dedup form:** Move the unload algorithm into a private helper (`_do_unload`) that is called by both `me unload` and `me moduleloader_unload`. This avoids the impl→free-function delegation issue since both callers would be `me` free functions. However this adds a new function rather than removing code, and must be weighed against anti-over-engineering rules.

3. **Leave as-is:** The duplication is not harmful — both bodies are identical and the guard clause prevents double-execution. The risk of silent divergence is low since `moduleloader_reload` calls `moduleloader_unload` (not `me unload`), so any future change to the algorithm will naturally land in `moduleloader_unload`.

---

## No commit made for A1

Per task instructions: "If anything blocks... write the blocker to `.sstack/semantic-dup-removal/A1_blocker.md` and stop — do NOT force the merge."
