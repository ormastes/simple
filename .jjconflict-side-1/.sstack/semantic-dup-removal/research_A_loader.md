# Research A: src/compiler/99.loader/ — Duplication Map

**Date:** 2026-04-28  
**Analyst:** Phase-2 Research Agent (Scope A)  
**Status:** Complete — advisor-reviewed

---

## Structural Note: Two `module_loader.spl` Files

The directory contains two files with the same name at different layers:

| Path | Role |
|------|------|
| `src/compiler/99.loader/module_loader.spl` | Compatibility surface. Header: `# Compatibility runtime module loader surface.` Imports types/JitInstantiator from `compiler.loader.*`. Provides `ModuleLoader` struct + `moduleloader_*` free functions using a path-tag heuristic + jit_cache rebuild on unload. |
| `src/compiler/99.loader/loader/module_loader.spl` | Full implementation. Uses `ResourceLifecycleManager`, `LoaderMapper`, `ObjectProvider`, SMF mmap, relocation application, validated loading. `moduleloader_unload` delegates to `lifecycle_unload_module`. |

These are **intentionally separated layers** — the top-level file is an explicit compatibility/interpreter shim over the real implementation. They must NOT be unified.

---

## Cluster 1: `me unload` vs `me moduleloader_unload` — identical bodies in the same file

- **Call sites (2 substantial):**
  - `src/compiler/99.loader/module_loader.spl:153–191` — `me unload(path: text)` method on `ModuleLoader`
  - `src/compiler/99.loader/module_loader.spl:304–341` — `me moduleloader_unload(self: ModuleLoader, path: text)` free function

- **Shared invariant:** Both encode exactly the same 38-line unload algorithm: (a) guard on `self.modules.has(path)`, (b) collect JIT symbols via `_collect_unload_jit_symbols`, (c) drop each from `self.jit`, (d) collect owned symbols via `owned_global_symbol_names`, (e) rebuild `global_symbols` from scratch via `global_symbols_without_names` + re-populate surviving JIT entries from `jit_cache`, (f) clear `loaded_metadata` via `loaded_metadata_remove_path`, (g) remove from `self.modules`. The file already follows the pattern of delegating impl methods to free functions: `me load` → `moduleloader_load`, `me moduleloader_resolve_generic` → `resolve_generic`. The `unload` pair missed this treatment.

- **Proposed unification:** `me unload` should delegate to `me moduleloader_unload`, exactly like `me load` delegates to `moduleloader_load`. No new helper is needed; the free function already exists. Change is:

  ```
  # Before (module_loader.spl:153-191):
  me unload(path: text):
      if not self.modules.has(path):
          return
      val remove_jit = _collect_unload_jit_symbols(self, path)
      ... [38 lines, body identical to moduleloader_unload] ...

  # After:
  me unload(path: text):
      moduleloader_unload(self, path)
  ```

  Owner file: `src/compiler/99.loader/module_loader.spl` (top-level). No new file needed.

- **Risk:** Low. The impl method is a pure delegator in the other paired methods. The only risk is the `me` mutation convention — `moduleloader_unload` is already declared `me`, so mutation semantics are preserved. No lifecycle ordering change; the algorithm is unchanged.

- **Test surface:**
  - Existing: `test/unit/compiler/loader/module_loader_spec.spl` calls `moduleloader_unload` (free function) at lines 106–107. `test/unit/compiler/loader/module_loader_crash_fix_spec.spl:23` also calls `moduleloader_unload` directly.
  - `test/unit/compiler/loader/module_loader_relocation_spec.spl:90` calls `loader.load(...)` (impl method path).
  - No existing test exercises `loader.unload(...)` via the impl-method path — which is why the duplicate body was never caught.
  - **Intensive test (interpreter-mode):** Add a test case to `module_loader_spec.spl` that: (1) loads a module via `loader.load(path)`, (2) calls `loader.unload(path)` (impl method), (3) asserts `loader.global_symbols` is empty, `loader.jit.jit_cache` has no entries for the module's symbols, `loader.jit.loaded_metadata` has no entry for path, and `loader.modules` has no entry for path. Run boundary cases: unload of non-loaded path (no-op), double unload (no-op second time), unload after JIT symbols were registered.

---

## Candidates Rejected by Anti-Over-Engineering Filter

### Rejected A: Top-level `moduleloader_unload` vs inner `loader/moduleloader_unload`

**Why rejected:** Different algorithms. Top-level uses a path-tag heuristic (`_symbol_matches_path`, rebuilds `global_symbols` from scratch by scanning `jit_cache`). Inner uses `lifecycle_unload_module` delegating to `ResourceLifecycleManager`, applies `lifecycle_on_symbol_mapped` tracking, and calls `loader_mapper`/`jit_mapper`. These are intentionally separated layers — the top-level header says "Compatibility runtime module loader surface." Unifying would merge a lifecycle-managed production loader with an interpreter-shim. Fails the "deliberately-separated layers" filter.

### Rejected B: `create_compiler_context` wrapping `compiler_create_context` (compiler_ffi.spl:366–371)

**Why rejected:** Two sites total. `create_compiler_context` is explicitly commented "workaround for struct constructor limitations." `compiler_create_context` is the real implementation; `create_compiler_context` is a legacy alias. Both are exported from `loader/__init__.spl`. This is dead-wrapper cleanup (alias removal), not a duplication cluster. Actionable as a separate cleanup: delete `create_compiler_context` and update the one non-scope caller if any, but do not include in a dedup cluster.

### Rejected C: `_name_in` duplicated in `unload_ownership.spl:3` and `module_loader.spl:23`

**Why rejected:** 4-line function, 2 sites. `unload_ownership.spl` is already imported by `module_loader.spl` (line 8: `use compiler.loader.unload_ownership.{owned_global_symbol_names, global_symbols_without_names}`). The fix is to add `_name_in` to the import — but `_name_in` is a private (underscore-prefixed) helper, so it would need to be exported or renamed. The duplication is 4 trivial lines. Fails the "fewer than 3 sites and trivial" filter.

### Rejected D: `moduleloader_allocate_exec_module` vs `moduleloader_allocate_exec_jit` (loader/module_loader.spl:614–630)

**Why rejected:** 2 sites. Each uses a different mapper (`loader_mapper` vs `jit_mapper`) with different policy (`allow_replace` parameter vs always-replace). A unified helper would need those as parameters, making the helper longer than the duplication. Fails the "unified helper longer than duplication" filter.

---

## Summary

| Cluster | Action | File |
|---------|--------|------|
| 1 — `me unload` body duplicates `me moduleloader_unload` | Proceed: make `me unload` delegate | `module_loader.spl` (top-level) |
| B — `create_compiler_context` alias | Flag only: legacy alias cleanup, not dedup | `loader/compiler_ffi.spl` |
| A, C, D | Rejected | — |
