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

## Follow-up (same day): retention at coordinator start

Statically reviewed only, like the fix above.

Fix item 1 left no process of a sharded or coordinator-lane build to run
retention: workers carry a shard role, the bootstrap coordinator installs
`SIMPLE_MIR_SHARD_LINK` before its in-process link, and the full-CLI
coordinator sets `SIMPLE_NATIVE_BUILD_WORKER=1` around its own compile
(`src/app/cli/native_build_main.spl`). A cache used only by such builds grew
without bound.

- **Where the pass runs now.** The top-level coordinator runs it once, right
  after build-start memory admission and before any prepass, resume adoption or
  worker spawn: `native_build_cache_scope_retention_at_start_v1`
  (`src/app/cli/native_build_main.spl`), called from
  `run_native_build_worker_inner` and from the bootstrap CLI's
  `_bootstrap_admit_native_build_memory_v1` (`src/app/cli/bootstrap_main.spl`,
  all four routes). Because nothing of this build exists yet, the pass cannot
  remove a scope the build has published into.
- **Who is refused.** `native_cache_scope_start_retention_due_v1`
  (`native_mir_shard.spl`) returns false for any role environment value
  (`SIMPLE_MIR_SHARD`, `SIMPLE_HIR_SHARD`, `SIMPLE_PARSE_SHARD`,
  `SIMPLE_MIR_SHARD_LINK`, `SIMPLE_FILE_WORKER_UNIT`,
  `SIMPLE_NATIVE_BUILD_WORKER`), for a grouped child
  (`SIMPLE_NATIVE_GROUP_RESULT`), for the MIR export-summary child
  (`SIMPLE_MIR_SHARD_EXPORT_WRITE`), and for a role flag in argv
  (`--file-worker`, `--parse-shard`, `--parse-fibers`, `--hir-shard`,
  `--mir-shard`; bootstrap children carry the flag and no role environment).
- **Once.** The coordinator exports `SIMPLE_NATIVE_CACHE_SCOPE_RETENTION_DONE=1`
  before it does any work. The same process (the bootstrap route re-enters
  `run_native_build_worker` in process) and every descendant that inherits its
  environment are refused from then on.
- **Liveness.** (a) The existing idle rule: a scope whose `.last-use`, own
  mtime or newest direct child mtime is within 21,600 s is kept. (b) Before the
  pass, every scope named by an object sidecar of the ledger this launch may
  resume from (`mir-run-latest` under the ledger root) gets a fresh `.last-use`
  (`native_mir_shard_ledger_scope_dirs_v1`,
  `native_cache_scope_start_retention_v1`). If a prior-ledger scope were removed
  anyway, adoption requeues its rows as `object-missing`; nothing fails.
- **Scope shape.** `native_cache_scope_dir_of_object_v1` matched any
  33-character component starting with `s`. It now requires `s` + 32 lowercase
  hex (`native_cache_scope_name_valid_v1`), the shape
  `driver_native_build_cache_scope_for_compiler_id` produces.

Limits of the follow-up:

- **Explicit `--cache-dir` only.** The pass runs on the directory given by
  `--cache-dir`. That is the one case where the coordinator provably names the
  directory its workers write scopes into; the sanctioned bootstrap
  (`scripts/bootstrap/build-phase3-phase4.sh`) passes it on every stage. Not
  covered, so still unbounded for
  sharded and coordinator-lane builds: no `--cache-dir` (the worker picks
  `build/native_cache`, a profile segment under `SIMPLE_NATIVE_BUILD_CACHE_DIR`,
  or the machine cache root), and the `planner-<sha>` / `collection-<sha>`
  sub-caches the full CLI derives below `--cache-dir`
  (`src/app/io/_CliCompile/compile_targets.spl`).
- **The build's own scope is not exempt.** The coordinator does not know its
  scope name, so the pass has no current scope: beyond the idle window it keeps
  `SIMPLE_NATIVE_CACHE_SCOPES_KEEP` - 1 scopes (5 by default). A build whose own
  scope was idle for more than 6 hours and is not among those loses its warm
  objects and recompiles.
- **No live-build marker exists.** A scope holds `phase.marker` and
  `.cache_scope`, both rewritten on each native compile and so already counted
  by the idle rule; nothing records a running process or its ledger. A
  concurrent independent build sharing the cache directory can therefore still
  lose a scope when all of these hold: its ledger names an object in the scope,
  the scope is not its own compile scope (rows adopted from a prior run, or
  published by another compiler identity), no row naming the scope was
  published or adopted in the last 6 hours, it has not reached link admission,
  and another top-level build starts (or an unsharded build compiles) with more
  than the kept number of scopes present. The link then fails with the "no
  longer in the native cache" message and a re-run recompiles the missing
  modules. Workaround: give concurrent long builds separate `--cache-dir`
  directories. A `SIMPLE_CACHE_SCOPE` lane alone is not enough: it changes the
  scope name, but every lane's scopes sit side by side in `<cache-dir>/s<32hex>`
  and one lane's pass scans and can remove another lane's.
- **New exposure from this follow-up.** After the first fix no sharded build
  pruned at all, so two sharded builds on one `--cache-dir` could not hurt each
  other. Now the start of one is a retention pass over the other's scopes,
  under the conditions above.
- **Once per process tree, not per build.** A long-lived process that runs
  several coordinator builds prunes only on the first, and a build started from
  inside another build inherits the latch and does not prune.
- An in-process unsharded build still runs the driver's own pass on its first
  native compile, as before.

## Known limits

- No process of a sharded or coordinator-lane build ran retention after fix
  item 1. The follow-up section above restores it for an explicit
  `--cache-dir`; the other cache directories stay unbounded for those lanes.
- The marker refresh depends on a file rewrite moving the marker's mtime. The
  marker now carries the write time as content so the write is never empty;
  this was not observed on a filesystem.
- The byte-cap sweeps (`disk_bound_enforce`, `disk_cache_admit_v1`) target the
  runtime object, HIR and warm-artifact directories. No caller passes a scope
  directory, so they are not a second path to this failure.
- A separate build sharing the cache can still remove a scope that a running
  build has not referenced through a ledger row for more than 6 hours. The
  exact conditions and the workaround are in the follow-up section.
- Not verified by execution: no runnable `simple` binary was used and no build
  was run while the fix was written.

## Specs

- `test/01_unit/compiler/driver/native_cache_scope_live_build_eviction_spec.spl`
- `test/01_unit/lib/nogc_sync_mut/io/disk_bound_spec.spl`
  ("a scope with a fresh liveness marker is not evictable", "the idle window
  is inclusive at its edge and never covers a future time")
