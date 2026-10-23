# Stage-2 RSS grows without bound once b065988b5a2 lands; not a seed thread-count problem

- **Date:** 2026-10-23
- **Status:** open. Root-cause hypothesis is from reading the code; no fix is applied and nothing was rebuilt (shared host).
- **Area:** Rust runtime transient heap scopes (`rt_transient_heap_promote`) and the stage-2 parser's per-file promotion
- **Evidence:** `C:/dev/wt-rel3-new/build/rss/jobs40.curve`

## Symptom

The stage-2 Simple compiler is built for x86_64-pc-windows-gnu: LLVM, `--entry-closure`, `--mode dynload`, falling back to one-binary.

| tree | jobs | RSS |
|---|---|---|
| `8aaa2501af6` (no `b065988b5a2`) | 16 | peak about 10 GB |
| `658410feaaf` (has `b065988b5a2`) | 24 | 56 MB, then 1.4 GB, 4.7 GB and 27 GB in about 4 minutes |
| `658410feaaf` | 40 | 41 GB at 745 s, 61 GB at 778 s, 82 GB at 811 s (about 600 MB/s); killed |

The 24-job run grows about as fast as the 40-job run. So growth does not follow the thread count; it follows the tree. In the 40-job curve, RSS stays under 300 MB until about 487 s and then grows steeply and steadily. That shape is a cumulative leak. A wider fan-out would instead show a high plateau.

## Root cause (hypothesis)

`b065988b5a2` ("fix(runtime): promote scope-owned heap roots; stage-2 surface_build SEGV") changed the early exit in `rt_transient_heap_promote`. On `release_phase3` the change is at `src/compiler_rust/runtime/src/value/collections.rs:2877-2885`:

```rust
let scope_owned = TRANSIENT_HEAP_SCOPE.with(|slot| { ... scope.objects.iter().any(|o| o.as_heap_ptr() == root_ptr) });
if !scope_owned && super::heap::is_registered_heap_ptr(root_ptr) { return true; }
```

Before this change, every registered heap root took the no-op exit. After it, a root that the current scope owns takes the full walk instead. That walk is at `collections.rs:2913-2965`. It does three things:

- It walks everything reachable from the root, including conservatively scanned raw-struct words.
- It removes every reached object from `scope.objects` (`scope.objects.retain(...)`).
- It promotes every reached raw block (`rt_transient_raw_promote`).

A promoted object is no longer freed when the scope ends, and **nothing ever frees it later**. No demote or release path exists.

That is the right outcome for the root the original bug needed: the retained parse `Result<ParserModule>`. It is the wrong outcome for the other per-file callers, which now run the full walk on every file:

- `src/compiler/10.frontend/core/parser.spl:158-166` (`parser_promote_transient_owners`, called once per parsed file from `src/compiler/80.driver/driver_source_pipeline_parsing.spl:290`) promotes these slots:
  - `par_errors`, `par_warnings` and `par_struct_names`. They are **reassigned to fresh arrays for every file** (`parser.spl:342-344`, `528`, `586`, `1419-1423`). Each file's arrays are allocated inside that file's scope, so they are scope-owned and are now promoted. The next file's `par_errors = []` then orphans them for good.
  - `par_kind_slot`, `par_text_slot`, `par_line_slot` and `par_col_slot` (`parser.spl:346-349`). The walk follows every token text these slots hold.
  - `type_pools_promote_hir_owners()` (`src/compiler/10.frontend/core/types.spl:1624`). It promotes the type-pool globals, and its own comment says the parser resets them inside each per-file scope.
- More `rt_transient_heap_promote` call sites exist in about 24 `.spl` files, for example `ast_coverage_inventory.spl:59-68` and `aspect_registry.spl:47`. Each one now runs the full walk whenever its root was allocated in the current scope.

So each parsed file permanently leaks its diagnostics arrays, its type-pool snapshot, and everything the conservative walk reaches from them. Before the change, all of these were freed at scope end.

Over the roughly 1,488-file closure, this adds up to tens of GB. More jobs only make the leak faster, which matches the 24-job and 40-job data. A side cost: the new ownership check is a linear scan of `scope.objects` on every promote call. That costs CPU in proportion to scope size, but it does not grow memory.

## Minimal fix (proposed, not applied)

Make promotion apply only to values that escape the scope. Do not promote every registered root that the scope happens to own. The smallest correct change is in the Simple callers; the runtime gate stays as it is, because the `ParserModule` SEGV fix needs it:

1. In `parser_promote_transient_owners`, stop promoting the per-file diagnostics: `par_errors`, `par_warnings` and `par_struct_names`. They are reset at the next `parser_init*`, so nothing reads them after the scope ends. If a caller does read them after the scope, that caller should copy out what it needs before the scope ends.
2. Promote the token slots (`par_*_slot`) only on the first parse in the process, which is what the comment above the function says. Use a `par_slots_promoted: bool` flag. Later files reuse those slots, which are already promoted, and do not re-walk them.
3. In `type_pools_promote_hir_owners`, promote only when the pool root was reallocated since the last promotion: track the generation or pointer. Do not re-walk and re-promote a fresh per-file copy every time.

An alternative on the runtime side is larger: record promoted roots and give them a release path (`rt_transient_heap_unpromote`) for when a global slot is overwritten. Prefer the caller fix.

**Verification to run once the host is free:** run the 24-job stage-2 build with RSS sampling and check that RSS stays at or below the `8aaa2501af6` envelope (about 10 GB at 16 jobs). Then run 40 jobs with `SIMPLE_MEMORY_LIMIT_MB=60000` as a hard stop.

## Seed native-build side (checked and ruled out as the primary cause)

- `src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:456-545` (`compile_entries_parallel`): this is a rayon `par_iter`. Each file gets a **fresh** worker thread (`compile_file_safe`, `compiler.rs:1100-1200`), so thread-local caches die with each file. The `module_cache.rs:530-545` caches have no bound, but they are per thread and freed when the thread exits. The parsed-source cache is capped at 256 per worker (`module_cache.rs:54`). Object bytes go straight to disk (`compiler.rs:524-525`), so they do not pile up in memory.
- `ModuleImports` (`mod.rs:545+`) is made of `Arc` fields, and the suffix index is shared once through `Arc` (`compiler.rs:478`). Cloning per worker is cheap, and nothing clones a whole-graph structure per worker.
- One real hazard remains, though it is not this bug: a timed-out worker cannot be cancelled (`wait_for_compiler_thread`, `compiler.rs:1243-1265`). It keeps its LLVM context alive until it finishes. `NativeCompileAdmission` (`compiler.rs:1080-1098`) only refuses **new** admissions after a timeout. It is a timeout latch, not a memory budget.

## Existing knobs that bound memory today

- `--threads N`, `SIMPLE_BOOTSTRAP_THREADS` and `--low-memory` (forces 1 worker). The default number of LLVM workers is clamped to 4 (`mod.rs:299`, `LLVM_DEFAULT_MAX_THREADS`). None of these is aware of RSS.
- `SIMPLE_MEMORY_LIMIT_MB` (`compiler/src/watchdog.rs:38-42`, `memory_guard.rs:32`) aborts the process above an RSS cap. It is a kill switch, not admission control.
- `SIMPLE_MODULE_RSS_WARN_MB` (`memory_guard.rs:38-42`) only warns.
- `SIMPLE_PARSED_SOURCE_CACHE_MAX` caps the seed's per-worker parse memo.
- No RSS-aware admission exists. If one is wanted, the place for it is `NativeCompileAdmission::run`: block admission while process RSS is above a `SIMPLE_NATIVE_RSS_BUDGET_MB`. It would not fix the leak above.
