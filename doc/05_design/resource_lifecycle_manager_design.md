# Resource Lifecycle Manager — Unified Deallocation for Loader & Interpreter

**Date:** 2026-02-22
**Status:** COMPLETE — All 5 phases implemented
**Scope:** `src/compiler/99.loader/`, `src/compiler/10.frontend/core/interpreter/`, `src/runtime/runtime.c`

---

## Problem Statement

Both the compiled-module loader (`ModuleLoader`) and the tree-walking interpreter have memory leak paths where JIT code pages, metadata, file-backed mmaps, and source text are never freed:

| Resource Class | Loader Path | Interpreter Path |
|---|---|---|
| Executable pages (RX mmap) | Freed on explicit `moduleloader_unload` only | N/A (no mmap) |
| JIT pages (`__jit__` owner) | **LEAKED** — `unmap_owner(path)` misses `__jit__` pages | N/A |
| SMF file mmaps (PROT_READ) | **LEAKED** — `smf_cache` never evicted per-module | N/A |
| Template metadata (`loaded_metadata`) | **LEAKED** — never removed from dict | N/A |
| Compiler context handle | **LEAKED** — `compiler_destroy_context` never called | N/A |
| Source text (`lex_source`) | N/A | **LEAKED** — overwritten, C `malloc`'d string not freed |
| AST arena nodes | N/A | **LEAKED** — only bulk-reset, no per-module cleanup |
| Value arena (C strings) | N/A | **LEAKED** — `val_reset()` clears arrays but no `spl_free_value` |
| Function table entries | N/A | **LEAKED** — never selectively removed |
| `rt_exec_manager_cleanup` | **NO-OP STUB** in `runtime.c:1108` | Soft JIT `tmp/jit/` files not cleaned |

### Root Causes

1. **No shared lifecycle interface** — loader and interpreter each have partial cleanup, neither complete.
2. **No ownership tracking for JIT-triggered symbols** — JIT symbols get `owner_id: "__jit__"` but the triggering module path is lost.
3. **No reference counting or generation sweep** — `SharedExecMapper.generation` is stored per-record but never used for eviction.
4. **Interpreter uses arena-global state** — no per-module isolation, so no selective unload possible without tracking decl-id ranges.

---

## Design: ResourceLifecycleManager

A single coordinator that both the loader and interpreter delegate to for tracking and freeing all resource classes.

### Architecture

```
ResourceLifecycleManager
  |
  +-- OwnershipRegistry            # Tracks what each module owns
  |     owner_resources: Dict<text, OwnedResources>
  |     jit_origin: Dict<text, text>   # jit_symbol -> triggering module
  |
  +-- SharedExecMapper (existing)   # Executable page management
  |
  +-- SmfCacheManager (wraps SmfCache)  # Per-module ref-counted mmap
  |     ref_counts: Dict<text, i32>
  |
  +-- InterpreterResourceTracker    # Per-module decl/func/value ranges
  |     module_decl_ranges: Dict<text, (i64, i64)>   # module -> (first_did, last_did)
  |     module_func_names: Dict<text, [text]>         # module -> registered fn names
  |     module_struct_names: Dict<text, [text]>       # module -> registered struct names
  |     module_global_names: Dict<text, [text]>       # module -> global var names
  |
  +-- GenerationSweeper             # Epoch-based unused code reclamation
        current_epoch: i64
        symbol_last_used: Dict<text, i64>  # symbol -> last-used epoch
```

### OwnedResources — Per-Module Resource Manifest

```simple
struct OwnedResources:
    module_path: text
    exec_symbols: [text]       # symbols mapped in SharedExecMapper
    jit_symbols: [text]        # JIT symbols triggered by this module
    smf_cache_paths: [text]    # SMF file paths used by this module
    metadata_paths: [text]     # loaded_metadata entries
    load_generation: i32       # generation at load time
    load_time: i64             # timestamp
```

### Key Methods

```simple
struct ResourceLifecycleManager:
    registry: OwnershipRegistry
    exec_mapper: SharedExecMapper
    smf_cache: SmfCacheManager
    interp_tracker: InterpreterResourceTracker
    sweeper: GenerationSweeper
    config: LifecycleConfig

impl ResourceLifecycleManager:
    # ---- Registration (called during load) ----

    me on_module_load(module_path: text):
        """Start tracking a new module."""
        self.registry.owner_resources[module_path] = OwnedResources(
            module_path: module_path,
            exec_symbols: [],
            jit_symbols: [],
            smf_cache_paths: [],
            metadata_paths: [],
            load_generation: self.exec_mapper.generation,
            load_time: current_time()
        )

    me on_symbol_mapped(module_path: text, symbol: text):
        """Record that a symbol was mapped for a module."""
        self.registry.owner_resources[module_path].exec_symbols.push(symbol)

    me on_jit_triggered(triggering_module: text, jit_symbol: text):
        """Record JIT symbol origin so unload can find it."""
        self.registry.jit_origin[jit_symbol] = triggering_module
        self.registry.owner_resources[triggering_module].jit_symbols.push(jit_symbol)

    me on_smf_accessed(module_path: text, smf_path: text):
        """Track SMF cache usage per module."""
        self.smf_cache.ref_count_inc(smf_path)
        self.registry.owner_resources[module_path].smf_cache_paths.push(smf_path)

    me on_metadata_loaded(module_path: text, metadata_path: text):
        """Track loaded_metadata per module."""
        self.registry.owner_resources[module_path].metadata_paths.push(metadata_path)

    # ---- Interpreter tracking ----

    me on_interp_module_parsed(module_path: text, first_did: i64, last_did: i64):
        """Record the decl-id range for an interpreter module."""
        self.interp_tracker.module_decl_ranges[module_path] = (first_did, last_did)

    me on_interp_func_registered(module_path: text, func_name: text):
        """Track function table entries per module."""
        self.interp_tracker.module_func_names[module_path].push(func_name)

    me on_interp_struct_registered(module_path: text, struct_name: text):
        """Track struct table entries per module."""
        self.interp_tracker.module_struct_names[module_path].push(struct_name)

    # ---- Unload (the core method) ----

    me unload_module(module_path: text):
        """Fully unload a module and free ALL associated resources."""
        if not self.registry.owner_resources.contains_key(module_path):
            return

        val owned = self.registry.owner_resources[module_path]

        # 1. Free JIT symbols that this module triggered
        for jit_sym in owned.jit_symbols:
            _ = self.exec_mapper.unmap_symbol(jit_sym)
            self.registry.jit_origin = self.registry.jit_origin.remove(jit_sym)

        # 2. Free loader-mapped symbols (existing path)
        _ = self.exec_mapper.unmap_owner(module_path)

        # 3. Evict SMF cache entries (ref-counted)
        for smf_path in owned.smf_cache_paths:
            self.smf_cache.ref_count_dec(smf_path)
            # Actually close mmap only when refcount hits 0

        # 4. Remove metadata entries
        for meta_path in owned.metadata_paths:
            # jit.loaded_metadata.remove(meta_path)  -- caller handles
            pass

        # 5. Interpreter cleanup (if applicable)
        if self.interp_tracker.module_func_names.contains_key(module_path):
            val func_names = self.interp_tracker.module_func_names[module_path]
            for name in func_names:
                func_table_remove(name)

            val struct_names = self.interp_tracker.module_struct_names[module_path]
            for name in struct_names:
                struct_table_remove(name)

            val global_names = self.interp_tracker.module_global_names[module_path]
            for name in global_names:
                env_remove_global(name)

            self.interp_tracker.module_decl_ranges = self.interp_tracker.module_decl_ranges.remove(module_path)
            self.interp_tracker.module_func_names = self.interp_tracker.module_func_names.remove(module_path)
            self.interp_tracker.module_struct_names = self.interp_tracker.module_struct_names.remove(module_path)
            self.interp_tracker.module_global_names = self.interp_tracker.module_global_names.remove(module_path)

        # 6. Remove ownership record
        self.registry.owner_resources = self.registry.owner_resources.remove(module_path)

    # ---- Sweep (epoch-based reclamation) ----

    me mark_symbol_used(symbol: text):
        """Called on every function call to update last-used epoch."""
        self.sweeper.symbol_last_used[symbol] = self.sweeper.current_epoch

    me advance_epoch():
        """Advance the epoch counter (called periodically)."""
        self.sweeper.current_epoch = self.sweeper.current_epoch + 1

    me sweep_unused(max_age: i64) -> i32:
        """Free symbols not used within max_age epochs."""
        val threshold = self.sweeper.current_epoch - max_age
        var freed = 0

        var stale_symbols: [text] = []
        for (symbol, last_used) in self.sweeper.symbol_last_used:
            if last_used < threshold:
                stale_symbols.push(symbol)

        for symbol in stale_symbols:
            # Find owner and unmap
            val rec = self.exec_mapper.get_record(symbol)
            if rec.?:
                _ = self.exec_mapper.unmap_symbol(symbol)
                freed = freed + 1
            self.sweeper.symbol_last_used = self.sweeper.symbol_last_used.remove(symbol)

        freed

    # ---- Full teardown ----

    me destroy():
        """Release all resources (process exit or REPL restart)."""
        # Unload all modules
        var paths: [text] = []
        for (path, _) in self.registry.owner_resources:
            paths.push(path)
        for path in paths:
            self.unload_module(path)

        # Clear exec mapper (catches any orphaned symbols)
        self.exec_mapper.clear()

        # Clear SMF cache (force close all mmaps)
        self.smf_cache.force_clear()

        # Interpreter full reset
        eval_init()
```

### SmfCacheManager — Ref-Counted SMF mmap Wrapper

```simple
struct SmfCacheManager:
    cache: SmfCache
    ref_counts: Dict<text, i32>

impl SmfCacheManager:
    me ref_count_inc(path: text):
        if self.ref_counts.contains_key(path):
            self.ref_counts[path] = self.ref_counts[path] + 1
        else:
            self.ref_counts[path] = 1

    me ref_count_dec(path: text):
        if self.ref_counts.contains_key(path):
            val new_count = self.ref_counts[path] - 1
            if new_count <= 0:
                # Evict from cache — calls munmap
                self.cache.evict(path)
                self.ref_counts = self.ref_counts.remove(path)
            else:
                self.ref_counts[path] = new_count

    me force_clear():
        self.cache.clear()
        self.ref_counts = {}
```

### InterpreterResourceTracker — Per-Module Interpreter State

The interpreter currently uses a global arena with no per-module boundaries. To enable selective unload, we need to track which names belong to which module.

```simple
struct InterpreterResourceTracker:
    module_decl_ranges: Dict<text, (i64, i64)>   # module -> (first_did, last_did)
    module_func_names: Dict<text, [text]>
    module_struct_names: Dict<text, [text]>
    module_global_names: Dict<text, [text]>
```

**New functions needed in interpreter:**

```simple
# In eval_tables.spl:
fn func_table_remove(name: text):
    """Remove a function from the function table by name."""
    # Find index in ft_keys, remove from ft_keys/ft_vals/ft_buckets/ft_nexts

fn struct_table_remove(name: text):
    """Remove a struct from the struct table by name."""

# In env.spl:
fn env_remove_global(name: text):
    """Remove a global variable binding."""
```

---

## Integration Points

### 1. ModuleLoader Integration

Replace `moduleloader_unload` body to delegate to `ResourceLifecycleManager`:

```simple
fn moduleloader_unload(self: ModuleLoader, path: text):
    # Delegate to lifecycle manager
    self.lifecycle.unload_module(path)

    # Also clean JIT bookkeeping
    val owned = self.lifecycle.registry.owner_resources[path]
    for sym_name in owned.jit_symbols:
        self.jit.drop_cached_symbol(sym_name)

    # Remove loaded_metadata entries
    for meta_path in owned.metadata_paths:
        if self.jit.loaded_metadata.contains_key(meta_path):
            self.jit.loaded_metadata = self.jit.loaded_metadata.remove(meta_path)

    # Remove from modules dict
    self.modules = self.modules.remove(path)
```

Hook `on_module_load`, `on_symbol_mapped`, `on_jit_triggered` into `moduleloader_load` and `moduleloader_resolve_symbol`.

### 2. JitInstantiator Integration

In `try_jit_instantiate`, after successful JIT compilation:

```simple
# Record JIT origin for later unload
self.lifecycle.on_jit_triggered(smf_path, entry.mangled_name)
```

### 3. Interpreter Integration

In `load_module` (interpreter module_loader.spl):

```simple
fn load_module(module_name, current_file):
    ...
    val first_did = ast_arena_len()  # record start
    parse_module_ast(source, path)
    val last_did = ast_arena_len()   # record end
    lifecycle.on_interp_module_parsed(module_name, first_did, last_did)

    register_module_functions()
    # also call lifecycle.on_interp_func_registered for each
    ...
```

### 4. Runtime C Layer

Fix `rt_exec_manager_cleanup` stub:

```c
void rt_exec_manager_cleanup(int64_t handle) {
    // Clean up soft JIT temp files
    char path[256];
    snprintf(path, sizeof(path), "tmp/jit/simple_soft_jit_%lld.spl", handle);
    remove(path);
}
```

Add `spl_free_all_values()` for bulk arena cleanup that properly frees C-side strings:

```c
void spl_free_all_values(SplValue* values, int64_t count) {
    for (int64_t i = 0; i < count; i++) {
        spl_free_value(values[i]);
    }
}
```

---

## Generation Sweep Strategy

The `SharedExecMapper.generation` counter is already incremented per `map_symbol` call. We extend this to an epoch-based LRU:

1. **Epoch advance:** Called periodically (every N function calls, or on timer).
2. **Mark:** Every function call through a JIT'd symbol updates `symbol_last_used[symbol] = current_epoch`.
3. **Sweep:** Configurable `max_age` (e.g., 100 epochs). Symbols not called within `max_age` epochs are candidates for eviction.
4. **Policy:** Only sweep JIT symbols (`owner_id == "__jit__"`). Loader-mapped symbols are stable and should not be swept unless the module is explicitly unloaded.

---

## File Layout

```
src/compiler/99.loader/loader/
    resource_lifecycle.spl          # ResourceLifecycleManager, OwnershipRegistry
    smf_cache_manager.spl           # SmfCacheManager (ref-counted wrapper)
    generation_sweeper.spl          # GenerationSweeper, epoch-based eviction

src/compiler/10.frontend/core/interpreter/
    interp_resource_tracker.spl     # InterpreterResourceTracker
    eval_tables.spl                 # + func_table_remove, struct_table_remove
    env.spl                         # + env_remove_global

src/runtime/
    runtime.c                       # Fix rt_exec_manager_cleanup, add spl_free_all_values
```

---

## Phased Implementation Plan

### Phase 1: Fix Immediate Leaks (No New Files) — DONE (2026-02-22)

1. **Fix `moduleloader_unload` to free JIT symbols.** In `moduleloader_unload`, also collect JIT symbols from `loaded_metadata[path].instantiations` that exist in `jit_cache`, and free them via `drop_cached_symbol` (which now also calls `exec_mapper.unmap_symbol`). **DONE** — `module_loader.spl:383-402`
2. **Fix `moduleloader_unload` to clear `loaded_metadata`.** Added `self.jit.loaded_metadata.remove(path)` after unmap_owner. **DONE** — `module_loader.spl:407-409`
3. **Fix `rt_exec_manager_cleanup`** — replaced no-op stub with `snprintf` + `remove()` for soft JIT temp files. **DONE** — `runtime.c:1108-1114`
4. **Add `SmfCache.evict(path)`** — closes single `MappedSmf`, updates stats, removes from cache. **DONE** — `smf_cache.spl:287-300`
5. **Fix `drop_cached_symbol` to free exec pages.** Added `exec_mapper.unmap_symbol(symbol)` call so mmap'd pages are freed when JIT bookkeeping is dropped. **DONE** — `jit_instantiator.spl:358-360`

### Phase 2: Ownership Registry — DONE (2026-02-22)

5. **Create `resource_lifecycle.spl`** with `OwnershipRegistry`, `OwnedResources`, `ResourceLifecycleManager`. Includes registration hooks (`lifecycle_on_module_load`, `lifecycle_on_symbol_mapped`, `lifecycle_on_jit_triggered`, `lifecycle_on_smf_accessed`, `lifecycle_on_metadata_loaded`), `lifecycle_unload_module` (frees JIT symbols, unmap_owner, SMF ref-counts), query functions, and `lifecycle_destroy` for full teardown. **DONE** — `resource_lifecycle.spl`
6. **Create `smf_cache_manager.spl`** with ref-counted SMF cache wrapper. `SmfCacheManager` wraps `SmfCache` with `ref_counts: Dict<text, i32>`. Evicts via `cache.evict(path)` when ref-count reaches zero. **DONE** — `smf_cache_manager.spl`
7. **Hook `lifecycle_on_module_load`, `lifecycle_on_symbol_mapped`, `lifecycle_on_jit_triggered`** into `ModuleLoader.load`, `resolve_symbol`, and `resolve_generic`. **DONE** — `module_loader.spl`
8. **Replace `moduleloader_unload` body** to delegate exec page and SMF cleanup to `lifecycle_unload_module`, then handle JIT bookkeeping and global_symbols cleanup. Exec unmap calls in `drop_cached_symbol` are idempotent after lifecycle frees. **DONE** — `module_loader.spl`
9. **Export new modules** from `mod.spl`: `resource_lifecycle.*`, `smf_cache_manager.*`. **DONE** — `mod.spl`

### Phase 3: Interpreter Tracking — DONE (2026-02-22)

10. **Create `interp_resource_tracker.spl`** with per-module parallel arrays (`irt_paths`, `irt_funcs`, `irt_structs`, `irt_enums`, `irt_globals`). Registration hooks: `irt_begin_module`, `irt_track_func`, `irt_track_struct`, `irt_track_enum`, `irt_track_global`. Unload: `irt_unload_module` calls all removal functions. **DONE** — `interp_resource_tracker.spl`
11. **Add removal functions** to interpreter tables. `func_table_remove`, `func_remove_return_type` (eval_tables.spl), `struct_table_remove` (eval_tables.spl), `enum_table_remove` (eval_tables.spl), `env_remove_global` (env.spl). All use chained hash map unlink + tombstone pattern. **DONE** — `eval_tables.spl`, `env.spl`
12. **Hook tracking into `load_module` and `register_module_functions`** — `irt_begin_module` called before registration, `irt_track_func`/`irt_track_struct`/`irt_track_enum` called during `register_module_functions`. **DONE** — `module_loader.spl`
13. **Add `interp_unload_module`** — calls `irt_unload_module` then clears `loaded_module_set` entry. Reset via `irt_init()` in `module_loader_init()`. **DONE** — `module_loader.spl`

### Phase 4: Generation Sweep — DONE (2026-02-22)

13. **Create `generation_sweeper.spl`** with `GenerationSweeper`, `SweeperConfig`, `SweeperStats` structs. Functions: `sweeper_new`, `sweeper_advance_epoch`, `sweeper_mark_used`, `sweeper_sweep` (finds stale symbols, unmaps via `exec_mapper.unmap_symbol`, respects `jit_only` flag), `sweeper_stale_count`, `sweeper_stats`, `sweeper_reset`. **DONE** — `generation_sweeper.spl`
14. **Integrate sweeper into ResourceLifecycleManager.** Added `sweeper: GenerationSweeper` field, `lifecycle_mark_used`, `lifecycle_advance_epoch`, `lifecycle_sweep_unused`, `lifecycle_sweeper_stats` delegation functions. New `lifecycle_new_with_sweeper` constructor for custom config. **DONE** — `resource_lifecycle.spl`
15. **Instrument compiled loader path.** `moduleloader_resolve_symbol` calls `lifecycle_mark_used(self.lifecycle, name)` at start of each resolution. **DONE** — `module_loader.spl`
16. **Instrument interpreter JIT path.** Added `jse_keys/jse_vals/jse_buckets/jse_nexts` parallel arrays and `jit_epoch` for sweep tracking. `jit_record_call` calls `jit_mark_symbol_used`. New functions: `jit_advance_epoch`, `jit_sweep_stale`, `jit_cleanup_symbol`, `jit_sweep_tracked_count`. **DONE** — `jit.spl`
17. **Export from `mod.spl`.** Added `export generation_sweeper.*`. **DONE** — `mod.spl`

### Phase 5: Full Teardown + Stats — DONE (2026-02-22)

18. **Enhanced `lifecycle_destroy`** to log stats before teardown (when verbose) and call `sweeper_reset` after clearing exec mapper and SMF cache. **DONE** — `resource_lifecycle.spl`
19. **Added `LifecycleStats` struct** with `tracked_modules`, `total_jit_symbols`, `smf_tracked_count`, `sweeper_epoch`, `sweeper_tracked`, `sweeper_stale` fields. `lifecycle_stats` aggregates from registry, smf_cache_mgr, and sweeper. **DONE** — `resource_lifecycle.spl`
20. **Wired cleanup into interpreter JIT.** `jit_cleanup` now clears `jse_*` arrays and resets `jit_epoch = 0`. **DONE** — `jit.spl`
21. **Test spec:** `test/unit/compiler/loader/generation_sweeper_spec.spl` — sweeper epoch advancement, mark used tracking, stale detection, stats, reset, lifecycle integration delegation. **DONE**

### Phase 6: Interpreter Module Loading Fixes — DONE (2026-02-22)

22. **Added DECL_USE processing to `eval_module()`** — Phase 1.5 between fn/struct registration and val/var evaluation. Previously, `use` statements were only processed in `eval_decl()` but `eval_module()` never called `eval_decl` for DECL_USE tags, so imported modules' symbols were never loaded at module eval time. **DONE** — `eval_stmts.spl`
23. **Module load depth guard** — Added `_module_load_depth` counter and `_MODULE_LOAD_MAX_DEPTH=16` to prevent runaway transitive loading. `load_module()` increments on entry, decrements on all exit paths, returns 0 if depth exceeded. **DONE** — `module_loader.spl`
24. **Selective import optimization** — `load_module_selective()` now checks if all `imported_names` already exist in `func_table_lookup()` before loading. Skips full module load if all symbols are already available (handles built-in functions). **DONE** — `module_loader.spl`
25. **Append-mode parsing** — Changed `parse_module_ast()` from `core_frontend_parse_isolated` (which calls `ast_reset()`, destroying caller's AST) to `core_frontend_parse_append` (preserves caller's AST). **DONE** — `module_loader.spl`

---

## Testing Strategy

### Compiled-Mode Tests (require compiled binary)

Both spec files are **compiled-mode only**. In interpreter mode, the test runner loads them as structural API documentation but cannot execute the `it` block bodies because:

1. **Loader modules** (`resource_lifecycle`, `smf_cache_manager`) have transitive FFI dependencies (`SharedExecMapper` → `smf_mmap_native` → `extern fn` for mmap).
2. **Interpreter modules** (`eval_tables`, `interp_resource_tracker`) are compiled as part of the interpreter's compilation unit. `eval_tables.spl` has a broken transitive import (`compiler.core.cfg_platform` should be `compiler.frontend.core.cfg_platform`), preventing standalone loading.

### Import Path Convention for Numbered Directories

Numbered directories (`NN.name/`) strip the numeric prefix during module resolution. When the numbered directory contains inner subdirectories (e.g., `99.loader/loader/`), the inner subdirectory name must appear in the import path:

```
# Directory structure:
#   src/compiler/99.loader/loader/resource_lifecycle.spl
#
# Correct import (includes inner "loader" subdirectory):
use compiler.loader.loader.resource_lifecycle.*
#
# Wrong import (skips inner subdirectory — file not found):
use compiler.loader.resource_lifecycle.*
```

Resolution trace for `compiler.loader.loader.resource_lifecycle`:
1. `compiler` → `src/compiler/` (direct match)
2. `loader` → `src/compiler/99.loader/` (numbered dir match, strips `99.`)
3. `loader` → `src/compiler/99.loader/loader/` (direct match — inner subdir)
4. `resource_lifecycle` → `src/compiler/99.loader/loader/resource_lifecycle.spl`

Similarly for interpreter modules:
```
# Directory structure:
#   src/compiler/10.frontend/core/interpreter/eval_tables.spl
#
# Correct import:
use compiler.frontend.core.interpreter.eval_tables.*
```

### Test Specs

- **Loader lifecycle:** `test/unit/compiler/loader/resource_lifecycle_spec.spl`
  - ResourceLifecycleManager registration (module tracking, symbol/JIT tracking)
  - SmfCacheManager ref counting (increment, decrement, eviction, multi-path, force clear)
- **Interpreter tracker:** `test/unit/compiler_core/interpreter/interp_resource_tracker_spec.spl`
  - Hash map removal functions (func_table_remove, struct_table_remove, enum_table_remove, env_remove_global)
  - InterpreterResourceTracker (begin_module, track_func/struct/global, unload, tombstoning)
- **Integration tests:** `test/unit/compiler/loader/leak_check_spec.spl`
  - Load/unload cycle, verify `EXEC_MEMORY_ALLOCS` is empty
  - Hot-reload cycle, verify old pages freed
  - Multiple modules sharing SMF, verify cache refcount
- **Valgrind/ASan:** Run `bin/simple leak-check` on test suite to verify no C-level leaks after implementing `spl_free_all_values`

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| Interpreter AST arena is shared; removing decl slots by index breaks other modules | Stale decl_ids crash | Don't remove AST slots — only remove func_table/struct_table entries. AST arena slots become dead but harmless. |
| `VAL_FUNCTION` values holding stale decl_ids after unload | Runtime crash on call | Mark unloaded decl_ids as `DECL_TOMBSTONE` (new tag). Check in `eval_function_call`. |
| Sweep evicting a symbol that's still reachable via stored function pointer | Crash on next call | Only sweep `__jit__` symbols. Loader symbols are stable. Add `pinned` flag for critical symbols. |
| Performance overhead of `mark_symbol_used` on every call | Slowdown | Use hash map with O(1) update. Skip marking for non-JIT symbols. |
