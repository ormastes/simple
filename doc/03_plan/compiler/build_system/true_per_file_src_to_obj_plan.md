# True per-file src->obj build plan (2026-10-27)

Goal: each worker takes one file through parse -> HIR -> MIR -> obj in one
process. First object in <= 10 s. No global parse barrier and no whole-closure load.
The coordinator set the order: closure publication first, TLDR second, #4962 after.
Ordering note: #4962 (PR3) is already reviewed. Consider landing it BEFORE PR2c so
PR2c does not have to rebase over it (PR2a and PR2b do not touch its files).
Location: `doc/03_plan/compiler/build/` does not exist and `compiler/` is already
over the fan-out limit, so this plan lives in `build_system/` (2 -> 4 files).

Ref labels: refs marked `[branch-only]` exist only on branch
`work/per-file-single-process-pipeline` (not on release/1.0.0); everything else
is on release/1.0.0.

## Measured baseline (phase-3 stage3 build, C:/dev/p3new/build.log)
- The log has no per-line timestamps. File birth was 08:25:44 and last write
  08:37:37 (11m53s). It has 61 lines and no object emitted yet.
- Line 4 `[capsule-shard] parse shards=8`. Shard 0 exits at line 21 and the last
  shard (7/8) at line 28. `[file-worker] workers=9` is at line 34.
- 17 `[parse-closure] selected=1525` lines = 8 coordinator shards + 1 per worker.
  Each of the 9 workers re-parses the full closure for ~6 min before its first
  HIR claim. Time-to-first-object is > 11m53s (no object yet).
- PR #4911 profile: 600/600 samples of a shard child were inside
  `native_build_publish_parse_closure_v1`, and 486 were in `_native_build_entry_closure`.

## Current code (release/1.0.0)
- Global parse shards: `src/app/cli/native_build_main.spl:666`
  `native_build_parse_shard_count`, `:750` `spawn_parse_shards`, `:786`
  `run_parse_shards` (runs `src/app/cli/parse_shard_main.spl`).
- Closure publication: `native_build_main.spl:2009` calls
  `native_build_publish_parse_closure_v1`
  (`src/app/cli/native_build_parse_closure_owner.spl:100`). The request is passed
  in `SIMPLE_PARSE_CLOSURE_REQUEST[_DIGEST]` and cleared at `:2015-2016` and
  `:2130-2131`, and in the owner at `native_build_parse_closure_owner.spl:96-97`.
- Worker entry: `run_native_build_worker` (`native_build_main.spl:1801`) clears
  the inherited request and re-walks the closure. This is the #4911 defect.
- `compile_targets.spl` sets the shard env inside the child at `:1482-1484` and
  clears the request for descendants at `:1537-1540`. A file worker therefore never
  inherits the request unless the parent passes an explicit marker.
- Further clear sites in the same area: `:1981`, `:2027`, `:2142`.
- Identity check: `native_entry_closure_request_identity_matches_v1`
  (`src/compiler/80.driver/driver_build/native_entry_closure_owner.spl:44`).
- Worker closure: `src/compiler/80.driver/driver_worker_surface_closure_v1.spl`
  follows imports transitively.
- Interface digest: `src/compiler/80.driver/cache/action_key.spl:184`
  `interface_digest_of`, `:221` `interface_digest_of_source`. The latter
  under-captures struct fields (`action_key.spl:195-215`, a filed bug), so this plan
  does NOT use it for dependent invalidation (see PR2b).
- No Invoker trait exists in owned code.

## Reused landed APIs (do not redefine)
- `SourceReader.read_src_async` / `update_tldr_async` / `await_now`
  (`cache/source_reader_v1.spl`).
- File-fiber parse under `SIMPLE_FILE_WORKERS=1`: `driver_build/file_fiber_v1.spl`.
- `module_artifact_publish_atomic_async_v1` (`cache/module_artifacts_v1.spl`) for
  every TLDR summary write.
- `CacheSingleFlightV1` (`cache/daemon/cache_single_flight_v1.spl`): call
  `complete_flight` then `forget`, or have waiters consume `future()`.
  It is IN-PROCESS only; cross-process coordination is specified in PR2b.
- Identity: XXH3 is only a lookup index. Persisted TLDR handles carry a sha256
  digest. `digest_admits_identity_v1` admits an ALGORITHM id (it checks that the
  digest algorithm is an allowed identity algorithm); it does not verify a digest
  value. The sha256 value comparison is done by the caller. In-process keys use
  runtime xxh3-128.
- The HIR cache key belongs to the HIR-cfg lane, not this plan.

## PRs (ordered, each small and landable)
Measure every PR: time-to-first-object, total wall time, and peak RSS under the
`capwatch.ps1` 8 GB cap on a small multi-file probe (5-10 files, 2-level imports).
`capwatch.ps1` is an external measurement harness (not repo code); the plan
assumes the operator has it, and any repo-side check must not depend on it.
Stage2 rebuilds are batched. One stage3 self-build at the end proves the batch;
there are no per-PR rebuilds.
Specs: every new spec under `test/01_unit/` gets a `test/unit/` mirror wherever
the test-tree divergence guard (`scripts/check/check-test-tree-divergence.shs`)
requires one; check the guard's pair list for each spec, do not assume.

### PR 1 - publish the closure once, make #4911 effective
- Files: `src/app/cli/native_build_main.spl` (`run_native_build_worker` :1801
  keeps the inherited request when the digest matches; drop the clearing at
  :2015-2016 on the success path); `native_build_parse_closure_owner.spl` (publish
  once after the #4922 authority step; the owner clears only on error);
  `driver_build/native_entry_closure_owner.spl` (identity match gates reuse).
- Also `compile_targets.spl`: the shard env is set inside the child (:1482-1484)
  and the request is cleared for descendants (:1537-1540). The parent must pass an
  explicit file-worker marker (env var carrying the request digest) so a file
  worker knows to reuse rather than re-walk. Review and adjust the remaining
  clear sites at :1981, :2027 and :2142 so none drops the request on the success path.
- Cleanup: pid-keyed closure-request dirs must be removed on normal exit, on error,
  and by a stale-pid sweep at the next start (owner pid not alive).
- Spec red->green: `test/01_unit/compiler/driver/parse_closure_reuse_spec.spl`.
  A worker with a valid request does zero closure walks. A digest mismatch fails
  closed and never silently re-walks. Also covers pid-dir cleanup. Mirror it in
  `test/unit/`.
- Integration spec: `test/02_integration/compiler/driver/parse_closure_walk_count_spec.spl`
  runs a real multi-worker native-build of the probe and counts real
  `[parse-closure]` walks; it expects exactly 1. Mirror it in `test/integration/`.
- Measure: the `[parse-closure]` walk count must be 1 in total (it was 17).

### PR 2 - remove the global parse barrier (three PRs)
A worker parses only its own files. Imports resolve through per-module TLDR
interface summaries; the worker never loads the closure.

#### PR 2a - per-stage driver entry points
- Split `compiler_driver_run_compile` into entry points for parse / HIR / MIR /
  emit. Behavior-preserving. The cache lane layers `lower_hir_async` /
  `lower_mir_async` / `emit_object_async` on these.
- Spec: `test/01_unit/compiler/driver/driver_stage_entry_parity_spec.spl`. Running
  the four stages in sequence gives an object byte-identical to the monolithic
  call on the probe. Mirror in `test/unit/`.
- Coordinate the stage signatures with the cache lane (its steps 1-2).

#### PR 2b - interface summary module (no route change)
- New `src/compiler/80.driver/cache/tldr_summary_v1.spl`. Produces and reads a
  per-module summary: exported decls, per-decl handles (`module_id + decl_id`,
  lazy), and a full-content digest.
- Target-neutral: the summary keeps ALL `@when`/cfg variants, per the
  HIR-target-neutral rule (HIR keeps every OS/CPU variant; MIR lowering picks the
  target). Reason: one summary serves every target, so a cross-target build needs
  no per-target re-production and the cache key has no target axis to get wrong.
  The alternative (key by target) multiplies summaries and invites stale-target
  hits. Selecting the active variant happens in the consumer's MIR lowering.
- Dependent invalidation uses a digest over the FULL summary content (sorted,
  canonical encoding of every exported decl including struct fields, generics,
  variants and body handles). It does NOT use `interface_digest_of_source`
  (`action_key.spl:195-215` under-captures struct fields; filed bug). The digest is
  sha256; `digest_admits_identity_v1` only vets the algorithm id.
- TLDR gap policies (each explicit):
  - Glob and bare imports (about 4,547 `use x.*` and 1,596 bare `use x`): the
    summary carries an exported-name list, so `use x.*` expands and a bare `use x`
    resolves member names without opening x's source.
  - Omitted param or return types: the summary producer infers them per module
    from that module's own HIR only. No cross-module inference at lookup time.
  - Generic bodies: the defining module's worker owns the generic body HIR and
    instantiation requests. The summary carries a body handle, loaded lazily for
    that one decl only, never the closure.
  - Macros: a macro needs fresh companions (summaries) for the imports it uses;
    the producer records them as dependencies of the macro decl.
  - Any remaining unsupported construct is a counted, logged per-module fallback
    (`[tldr-fallback] module=... reason=...`), never a silent closure load.
    Measure the fallback rate (fallbacks / modules) on the probe and the stage3
    batch; the gate is reported, and a rising rate is a regression.
- Concurrency:
  - `CacheSingleFlightV1` is in-process only. Across processes use a file lease:
    exclusive create of `<summary>.lease` holding the owner pid; liveness check on
    the owner pid; a dead owner's lease is stolen. The winner produces and
    publishes by atomic rename. Losers wait (bounded) or re-read the published file.
  - Windows: `MoveFileEx` fails while a reader holds the file open. Readers open
    with share-delete, or the publisher retries with bounded backoff (fail closed
    after the bound). Reads and publish both use `module_artifact_publish_atomic_async_v1`.
- Spec: `test/01_unit/compiler/driver/tldr_summary_spec.spl`. Covers in-process
  single-flight, cross-process lease (live owner, dead owner), atomic publish,
  rejection of a stale digest, struct-field change invalidating a dependent, glob
  and bare-import name lists, counted fallback, and a concurrent read during
  publish (Windows share-delete). Mirror in `test/unit/`.

#### PR 2c - route switch, behind a flag
- Files: `driver_worker_surface_closure_v1.spl` (replace the transitive walk with a
  summary lookup); `driver_source_pipeline_parsing.spl`; `native_build_main.spl`
  (take `run_parse_shards` :786 off the per-file route when the flag is on).
- Flag: `SIMPLE_TLDR_IMPORTS=1` (default off until the stage3 batch is green).
- Spec: `test/01_unit/compiler/driver/tldr_route_spec.spl`: a worker never opens
  sources it does not own; flag off keeps the old route. Mirror in `test/unit/`.
- Measure: per-worker RSS stays flat as closure size grows. No `parse shards=` line.

### PR 3 - finish #4962 hardening (one child per batch, fail closed)
Already reviewed. The Fable re-review of 97c856626e0 marked B1-B4 resolved. Prefer
landing this before PR2c. This PR lands that work and adds the following
(refs marked `[branch-only]` exist only on `work/per-file-single-process-pipeline`):
- B1: a lock failure returns `Err` (`driver_worker_surface_closure_v1.spl:380-391`
  `[branch-only]`). That becomes a compile error at
  `driver_source_pipeline_parsing.spl:757-759` `[branch-only]`. The loop refuses a
  zero-claim exit without the drained proof (`native_file_unit_loop_v1.spl:62-65`
  `[branch-only]`).
- B2: `worker_unit_pick_seal_v1` (`driver_worker_surface_closure_v1.spl:405-423`
  `[branch-only]`) clears the owner's picks. Picks left by a killed parent are
  counted unfinished by `driver_hir_recovery.spl:242-249` `[branch-only]`. Add a
  lease based on owner-pid liveness.
- B3: rebased onto release/1.0.0 (merge a630da4abbc). Re-run the ratchet.
- B4: `native_file_unit_loop_spec.spl` (8 cases) + `worker_unit_pick_spec.spl`
  (both `[branch-only]`).
- Still open: a module that is picked but never claimed
  (`native_file_unit_loop_v1.spl:59` `[branch-only]`) needs one real per-file lane run.

### PR 4 - leaf-first scheduling + time-to-first-object metric
- Files: `driver_build/native_file_unit_loop_v1.spl` (`[branch-only]`; order by
  import depth, leaves first); `native_build_main.spl` emits `[first-object] ms=`.
- Spec: `test/01_unit/compiler/driver/leaf_first_schedule_spec.spl`; mirror in
  `test/unit/`.
- Gate: time-to-first-object <= 10 s on the probe.

### PR 5 - async node tasks + one Invoker trait (after #4910)
- New `src/compiler/80.driver/driver_build/invoker_v1.spl`: `trait Invoker` with
  `ProcessInvoker` (one child per batch, from #4962) and `FiberInvoker`
  (`file_fiber_v1.spl`). This lane owns the trait.
- Spec: `test/01_unit/compiler/driver/invoker_parity_spec.spl`; mirror in
  `test/unit/`. Both invokers produce the same objects, and a child failure is an
  error in both.
- Measure: wall time and RSS for the fiber invoker vs the process invoker on the probe.
