# A long native-build evicted cache scopes its own link still needed

Status: fix proposed, statically reviewed only. Nothing was built or run.

## What happened

A pure-Simple `native-build` of the compiler itself (per-file worker lane,
1,611 modules, cache `~/.simple/prov/p3h/cache`) ran 07:50 to 15:08 on
2026-11-24. All 195 batches compiled with zero failed modules. The link child
then refused the ledger:

```
error: MIR shard module object missing: compiler.common.driver_compile_options
  (.../p3h/cache/s264d59a3c4d238c02222a5fc874a842c/aot-23f574aa...6a2539.o)
```

7h20m of compile was lost. The object count under the cache had fallen from
about 6,600 to 1,345 by the end of the run.

## Evidence

- The scope directory `s264d59a3c4d238c02222a5fc874a842c` no longer exists.
- After the failure the cache held about 170 `s<32hex>` scope directories. The
  oldest surviving one has mtime 08:26; the cache root was last modified at
  14:25. Everything written in the first half hour of the run is gone, which
  matches a 6 hour idle cutoff applied late in the run. This is post-hoc
  directory evidence: it is consistent with the mechanism below, it does not
  record which process ran the delete.
- An earlier run of the same build survived only because an external script
  touched every scope directory every 5 minutes.
- The failed run used an older pinned source in which each batch resolved to
  its own scope directory, so a scope written by batch 3 was never written
  again.

## Mechanism

`_compile_to_native_with_backend_session`
(`src/compiler/80.driver/driver_aot_native_output.spl`, the
`disk_bound_keep_newest_dirs(cache_dir, ..., "s", 33, keep 6, 21600)` call)
runs scope retention on every entry, with no check of the process role.

- **When it runs.** Every `compile_to_native` call. A shard worker calls it
  once per batch (`driver_aot_pipeline.spl` `aot_compile_mir_shard_v1`), and
  the link child calls it after admitting the ledger and before linking
  (`aot_link_mir_shards_v1`). So retention ran throughout the build, in every
  child, including in the link child after it had checked that the objects
  exist.
- **What idle means.** `disk_bound_keep_newest_dirs`
  (`src/lib/nogc_sync_mut/io/disk_bound.spl`) takes the newest mtime of the
  scope directory and its direct children. Only the caller's own scope gets a
  `.last-use` marker. Reading an object moves no mtime.
- **What it deletes.** Beyond the 6 newest scopes, every scope whose newest
  mtime is older than 21,600 seconds is removed whole (`dir_remove(..., true)`).
- **What protects a live build.** Nothing. The ledger sidecars that name the
  objects are never consulted.

A build longer than the window therefore deletes its own early output.

## State on release/1.0.0

PR #11162 made the scope identity stable per compiler, so one build's
children now share a scope and the caller's own scope is always skipped. The
hazard remains for a ledger that names objects in another scope (rows adopted
from a prior run by `native_mir_shard_resume_adopt_v1`, objects published by
another lane) and for any concurrent build whose scope is only read.

## Fix

1. Retention runs only in an unmarked top-level process.
   `native_cache_scope_eviction_role_allowed_v1` returns false when any of
   `SIMPLE_MIR_SHARD`, `SIMPLE_HIR_SHARD`, `SIMPLE_PARSE_SHARD`,
   `SIMPLE_MIR_SHARD_LINK`, `SIMPLE_FILE_WORKER_UNIT` or
   `SIMPLE_NATIVE_BUILD_WORKER` is set. In that process it runs once, on the
   first native compile, not again from later staged batches.
2. Every ledger row that names an object refreshes the `.last-use` marker of
   that object's scope: on PASS publish, on resume adoption, and on link
   admission (`native_cache_scope_dir_of_object_v1`,
   `disk_bound_mark_dir_used`). A scope a running build references is no
   longer idle to any other build.
3. The idle decision is the pure `disk_bound_dir_is_idle(used, now, min_age_s)`.
   The 6 hour policy for abandoned scopes is unchanged.
4. The link error separates "row is not CACHE_STORED" from "object file is
   gone" and says a re-run recompiles the missing modules. That is true:
   `native_mir_shard_resume_row_reason_v1` returns `object-missing` for such a
   row and requeues it.

No new extern is introduced.

## Known limits

- In a sharded build the workers carry a shard role, and the coordinator
  installs `SIMPLE_MIR_SHARD_LINK` in its own process before it links
  (`src/app/cli/bootstrap_main.spl`), so by reading the code no process of
  such a build runs retention. If that holds, the idle policy now runs only in
  unsharded top-level builds, and a cache used only by sharded builds is
  bounded by the number of compiler identities rather than by
  `SIMPLE_NATIVE_CACHE_SCOPES_KEEP`. Every lane was not traced.
- The marker refresh depends on a file rewrite moving the marker's mtime. The
  marker now carries the write time as content so the write is never empty;
  this was not observed on a filesystem.
- The byte-cap sweeps (`disk_bound_enforce`, `disk_cache_admit_v1`) target the
  runtime object, HIR and warm-artifact directories. No caller passes a scope
  directory, so they are not a second path to this failure.
- A separate unsharded build sharing the cache can still remove a scope that a
  running build has not referenced through a ledger row for more than 6 hours.
- Not verified by execution: no runnable `simple` binary was used and no build
  was run while the fix was written.

## Specs

- `test/01_unit/compiler/driver/native_cache_scope_live_build_eviction_spec.spl`
- `test/01_unit/lib/nogc_sync_mut/io/disk_bound_spec.spl`
  ("a scope with a fresh liveness marker is not evictable")
