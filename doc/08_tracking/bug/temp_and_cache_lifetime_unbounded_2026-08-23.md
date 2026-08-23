# Temp + cache lifetime is unbounded and partly unowned (2026-08-23)

**Status:** partly fixed (see §Fixed), remainder RECORDED not fixed.

## The premise that started this was wrong, and that matters

The reported symptom was "`native-build` without `--cache-dir` uses no cache at
all". **A default cache directory already exists on every path**, and has for a
long time:

| path | default when `--cache-dir` is omitted | site |
|---|---|---|
| Rust seed native-build | `<project_root>/.simple/native_cache` (+ target triple + `cache_scope_segment()`) | `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:679-701` (`cache_base_dir`/`cache_dir`) |
| pure-Simple `native-build` CLI | `build/native_cache` | `src/app/io/_CliCompile/compile_targets.spl:601,723` |
| pure-Simple SMF build cache | `build/smf`, env `SIMPLE_NATIVE_BUILD_CACHE_DIR` | `src/compiler/70.backend/build_native.spl:52-56` |
| front-end parse cache | `build/bootstrap/native_cache/<lane>/frontend` | `src/compiler/10.frontend/frontend_parse_cache.spl:78-86` |
| HIR cache | `build/bootstrap/native_cache/<lane>/hir` | `src/compiler/80.driver/driver_hir_cache.spl:84-89` |

`SIMPLE_CACHE_SCOPE` unset resolves to `default` in all of them. So "give it a
default" was not the fix; the directory was never the gate.

## What the actual gate is

`frontend_parse_cache_enabled()` requires a NON-EMPTY
`SIMPLE_FRONTEND_CACHE_SCOPE`, published only by
`_driver_publish_frontend_cache_scope()` (`driver_source_pipeline_parsing.spl:205`)
from two phase-2 call sites. `hir_cache_enabled()` delegates to the same scope.
Nothing else in the tree publishes it. A run that never reaches those two sites
has both caches OFF, with a perfectly good empty cache directory sitting there
— which is exactly the "zero `[frontend-cache]`/`[hir-cache]` receipts" that was
misread as a missing `--cache-dir` default.

Worse, `frontend_parse_cache_scope()` MEMOIZED the empty answer, so a single
early read latched both caches off for the rest of the process
(`frontend_parse_cache_scope_memo_latches_off_2026-08-23.md`).

## Fixed in this change

1. **Negative-memo latch.** `frontend_parse_cache_scope()` now memoizes only a
   non-empty scope, so a late publish is observed. Closes the filed latch bug.
2. **`rt_file_stat` returned the file SIZE under the interpreter.**
   `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs:289` answered
   `meta.len()`, while BOTH native runtimes return mtime seconds
   (`src/runtime/runtime.c:1967`,
   `src/compiler_rust/runtime/src/value/sffi/file_io/metadata.rs:315`).
   `std.io.file_modified_time` is a bare rename of this call, so every age
   computation under the seed silently used a byte count. Fixed to return
   mtime seconds. This is a correctness divergence between the interpreter and
   native runtimes, not just a cache concern.
3. **Size-capped LRU eviction** for the flat entry caches:
   `src/compiler/10.frontend/cache_dir_evict.spl`, wired into
   `frontend_parse_cache_store` and `hir_cache_store`. Default cap 4 GiB,
   `SIMPLE_CACHE_MAX_BYTES` overrides, `0` disables. Sweeps once every 512
   stores. `*.tmp` in-flight stores and any entry modified within 300 s are
   never evicted, so a live build's entry cannot be pulled out from under it;
   an entry is one self-contained file, so deletion is a single unlink and
   there is no half-deleted state a later run could read as a hit.
   Spec: `test/01_unit/compiler/frontend/cache_dir_evict_spec.spl`.

## RECORDED, not fixed

- **`*.simple-native-build-<pid>-<ts>.tmp` leaks on abnormal exit.**
  `compile_targets.spl:879` stages the output beside the requested `--output`
  and removes it on every *handled* failure path (`:1062,1067,1140`). A SIGKILL,
  an OOM, or the harness timeout leaves the staging file forever, and **nothing
  in the tree ever sweeps them** — no startup sweep, no script, no guard. Fix
  shape: at `:880`, list the output's parent and remove siblings matching
  `<output>.simple-native-build-*.tmp` whose pid is not live. Not done here
  because it needs a dir-listing helper on that path and a spec that can fake a
  dead pid.
- **`build/`, `.simple/`, `/mnt/data/tmp/` have no documented lifetime.**
  `doc/07_guide/infra/host_storage_layout.md` describes WHERE things live, not
  how long they live. There is no temp/scratch retention policy document at all
  — the only retention policy in `doc/07_guide/infra/` is for LOGS
  (`logging/log_retention_policy.md`). Per-lane native caches under
  `build/bootstrap/native_cache/<lane>/` accumulate one subtree per lane name
  ever used and are never reaped.
- **The CAS store's GC is still unwired.** `src/compiler/80.driver/cache/gc/`
  (`admission.spl`, `fast_gc.spl`, `mark_sweep.spl`) implements watermarks,
  leases, trash and quarantine against `cache_protocol.sdn` — for a store whose
  `cas_store.spl`/`action_key.spl` have no external callers (see
  `.claude/rules/commands.md`). The eviction added above deliberately does NOT
  build on it: adopting that layout for two flat hash-named directories would
  be strictly more machinery for strictly less certainty. Reconsider only if an
  entry dir exceeds ~100k files.
- **`fast_gc.spl` declares `rt_file_modified_time`, which exists nowhere.**
  One of the tree's 1,466 unbacked externs; on the native path it silently
  returns nil, so the whole tmp-age sweep in that file is inert. Not touched —
  deleting it is a separate decision, and `check-unbacked-extern-ratchet.shs`
  already freezes it.
