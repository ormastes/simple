# Concurrency Architecture — Lockless by Default

**Status:** Normative. **Adopted:** 2026-11-04 (owner decision).
**Scope:** all Simple code: compiler, stdlib, runtime, tooling, userland
services and apps. Kernel/driver HAL code may use locks only under the explicit
exception rule in §3.

## 1. Rule

Concurrency in Simple is **lockless by default**. Shared state is either
**immutable** or updated by **compare-and-swap (CAS)-style** publication. A lock,
mutex, or file lock is a documented exception. It is never the default tool.

## 2. Default primitives (in order of preference)

1. **Immutable / persistent data and content-addressed values.** Readers never
   block and never see torn state. Updates build a new value. Equal content
   means an equal name.
2. **Message passing / actors with ownership transfer.** This is the existing
   actor and async model
   ([async infrastructure](../async_infrastructure.md),
   [SimpleRing](../../simple_ring_async_base.md)). Rings stay single-owner.
   Values cross a boundary by move, not by shared mutation.
3. **Atomic CAS on small cells.** Atomically swap a pointer to an immutable
   value, use a versioned compare-and-swap, or append to a log whose entries
   are unique.
4. **Per-owner private state merged at read time.** Each writer owns its own
   shard. Readers fold the shards together, so there is no shared write cell.

### 2.1 Files and IPC across processes

- Write to a private temp file, then **publish with an atomic rename**.
- Use **content-addressed names**. Two writers producing identical content is a
  benign race: either rename wins and the result is the same.
- **No in-place writes** to a published file.
- Logs are **append-only, one file per event**, with unique names. Never use a
  shared append handle.
- Mutable "current" state is an **atomic pointer-file swap**: write a new
  pointer file and rename it over the old one. The pointer names an immutable
  object.

## 3. Locks: explicit exception only

Locks, mutexes, and file locks are allowed **only** where they are explicitly
specified and justified. Examples are an OS/driver HAL, a hardware register
sequence, or an external API that requires a lock. Every lock must:

- carry an explicit annotation or a documented exception with a named **owner**;
- be **bounded**, with a timeout or a bounded critical section;
- **fail closed** when acquisition fails or times out;
- **never be held across `await` or I/O**.

**Review rule:** a new lock without a documented exception is rejected in
review.

### 3.1 Documented exceptions

| Exception | Scope | Why | Owner | Exit |
|---|---|---|---|---|
| Cross-module mutable allocator globals (`pub var _g_*` in `src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/mimalloc_types.spl`) | Pure-Simple mimalloc port: heap, counters, options, delayed-free list. | The globals were already written from sibling modules (`mimalloc.spl`, `mimalloc_stats.spl`). Native codegen cannot import a non-public module static, so they were made `pub` (#8591). The read-modify-write counters (`_g_total_allocated = _g_total_allocated + size`) are not atomic. Concurrent use of these globals is unsupported: the `nogc_*` ports are used from one thread, and the `gc_async_mut` port has not been verified as single-threaded, so treat it as unsafe under concurrency until the accessor exit lands. | ormastes (repository owner), recorded by the early Phase 3 lane session 2026-11-12 | Replace with owner accessor fns (`TODO(mimalloc-accessors)` in each `mimalloc_types.spl`). Do not add new writers.
| `authority.lock` (`file_lock`, 10 s) in `src/compiler/80.driver/cache/shared_generation_store.spl` (6 sites) | Shared generation store: publish of the generation `CURRENT` pointer and orphan-stage reclaim. | Compare-then-replace of a pointer file plus a multi-entry reclaim; POSIX `rename` cannot compare. Bounded (10 s), fails closed (`authority-lock-unavailable`), no `await`/network under the lock. | compiler driver cache (80.driver), recorded by the lock/serial audit lane 2026-11-13 | Versioned pointer published by `rename` + read-back (CAS on the generation name), as `cas_batch_transaction` already stages its `CURRENT.tmp.<id>`.
| `CURRENT.lock` (`file_lock`, 30 s / 1 s) in `src/compiler/80.driver/cache/package_module_index.spl` (3 sites) | Package module index: graph writer vs binding-only fallback compare-and-replace of `CURRENT`. | A late fallback must not erase a graph published after its earlier read; the compare and the replace have to be one step. Bounded, fails closed (`false`). | compiler driver cache (80.driver), recorded 2026-11-13 | Same versioned-pointer CAS as above.
| `publication.lock` (`file_lock`, 5 s / 1 s) in `src/compiler/80.driver/cache/cas_batch_transaction.spl` (2 sites) and `cache/native_noop_admission.spl` (1 site) | CAS batch and native no-op receipt publication: compare `CURRENT` with the expected parent, then `rename` the staged pointer. | Conditional replace of `CURRENT`. Bounded, fails closed (`publish_conflict` / `publication-lock-unavailable`). | compiler driver cache (80.driver), recorded 2026-11-13 | Same versioned-pointer CAS as above.
| `.receipt-archive.lock` (`file_lock`, 5 s) in `src/compiler/80.driver/cache/gateway/scv_build_validation_receipt_archive_v1.spl` | SCV build-validation receipt archive: single-writer archive append + fsync. | Index append is read-modify-write. Bounded, fails closed (`build-receipt-lock-unavailable`). | compiler driver cache (80.driver), recorded 2026-11-13 | Per-receipt O_EXCL files with a derived index (no shared index file).
| `{queue}/.lock` (`file_lock`, 30 s) in `src/compiler/80.driver/driver_worker_surface_closure_v1.spl` (`worker_unit_pick_v1`, `worker_unit_pick_seal_v1`) and `driver_hir_recovery.spl` (3 sites, retry -> `HIR_SHARD_CLAIM_LOCK_TIMEOUT_V1`) | HIR shard claim ledger: `.pick` reclaim of a dead owner's pick and the seal/claim ledger walk. | Reclaiming a dead owner's `.pick` is a conditional overwrite that O_EXCL cannot express. Bounded, fails closed (`Err` / `-1` / typed timeout). The former flock in `driver_hir_cache.hir_shard_owns` was unreachable and removed 2026-11-13 (static split only). | HIR recovery/seal lane (fenced), recorded by the lock/serial audit lane 2026-11-13 | Owner-tagged `rename` of the pick record (`<pick>.<owner>` -> `<pick>`) with liveness in the record itself.
| `writer.lock` (POSIX `flock` on inherited FD 9) in `scripts/bootstrap/bootstrap-phase-verification.shs` (module-progress state) | Bootstrap phase verification: one module-progress writer per campaign. | Kernel-released when the campaign and all workers exit; competing writers refuse (`return 1`); no PID guessing, no stale-lock deletion. | bootstrap scripts, recorded 2026-11-13 | `mkdir`-claim of the state directory (as `run-native-incremental-adapter.shs` already does -- that one is an atomic claim, not a lock).
| Watcher single-instance lock (`src/compiler/80.driver/watcher/watcher_lock.spl` over `std.daemon_sdk.lock`, `.build/watcher/watcher.lock`) | Build watcher daemon: one instance per checkout. | Daemon singleton; bounded by the daemon SDK lease. | watcher/daemon SDK, recorded 2026-11-13 | Lease file with owner liveness published by `rename`.
| `phase-owner.lock` (`file_lock`, 1 s) in `src/app/bootstrap_builder/phase_admission.spl` (3 sites: open, retained re-open x2) | Managed phase admission: one parent owns a phase's state root for the admission's lifetime (`ManagedPhaseAdmissionV1` holds the handle). | Lifetime ownership of a state directory, not a critical section; a second parent must refuse, not wait. Bounded (1 s single try), fails closed (`Err("another parent owns phase admission")` / `"phase owner is still active"`). | bootstrap_builder managed-phase parent (buildrunner lane, `doc/00_llm_process/feature_expert/buildrunner/skill.md`), recorded by the lock/serial audit lane 2026-11-13 | Owner lease record published by `rename` with pid + start identity, refused while the recorded owner is live.
| `owner.lock` (`file_lock`, 1 s) in `src/app/build/scheduler/owner.spl` | Distributed build scheduler: exclusive lifetime owner of one trusted journal root. | Journal single-writer; fails closed (`lock-unavailable` state). NOTE the in-code comment "zero means wait forever" is wrong for `rt_file_lock`: timeout 0 is one non-blocking try (deadline = now). | Main scheduler role, dist_build_scheduler lane (`doc/03_plan/compiler/build_system/dist_build_scheduler_2026-09-25.md` § Ownership and contract), recorded 2026-11-13 | Fence-numbered journal publish by `rename` (the fence already exists in the design).
| `worker.lock` (`file_lock`, 1 s) in `src/app/build/scheduler/worker_execute.spl` (3 sites) and `worker_cleanup_ack.spl` (1 site) | One-shot Linux worker: one attempt executes / acknowledges cleanup per state dir at a time. | Attempt-private state; a busy worker refuses (`worker-busy`), unlock failure is a block (`worker-unlock-failed`). Held across OCI execution by design (documented in `doc/04_architecture/dist_build_scheduler.md`), which is the one place this doc's "never across I/O" rule is knowingly relaxed. | Node agent / worker role, dist_build_scheduler lane, recorded 2026-11-13 | Attempt directory claimed by `mkdir`; the parent already refuses a second action for a worker with an active ledger attempt.
| `.simple-build-export.lock` (`file_lock`, 1 s) in `src/app/build/scheduler/parent_artifact_export.spl` | Publication broker: one artifact export into a destination root at a time. | Destination tree write + fsync; fails closed (`destination-lock-unavailable`). | Publication broker role, dist_build_scheduler lane, recorded 2026-11-13 | Per-digest O_EXCL staging + `rename` of the final leaf.
| `.simple-clang-build.lock` (`file_lock`, 1 s) in `src/app/build/clang_policy/native_rebuild_barrier.spl` | CMake/Ninja protected-object invalidation barrier: one owner redirects the build root's stamps/outputs. | Multi-file barrier update; fails closed (`build-owner-unavailable`). | clang_policy (dist_build_scheduler lane, `skill.md` row for `clang_policy/*`), recorded 2026-11-13 | Barrier generation published by `rename` of a single manifest.
| `ARRAY_FREE_QUARANTINE` (`Mutex<HashSet<usize>>`) in `src/compiler_rust/runtime/src/value/heap.rs` (seed runtime) | Debug-only array-free quarantine: `rt_array_free` records the poisoned address, a registry miss checks it. | Exists only when `SIMPLE_ARRAY_FREE_QUARANTINE=1` (off by default; unset, the `OnceLock` holds `None` and no lock is taken). Critical section is one `HashSet` insert/lookup, no I/O, no `await`; a poisoned lock skips the record/check (diagnostic only, never on a production path). | seed JIT memory lane (`doc/05_design/compiler/jit_memory/seed_jit_array_reclamation.md`), recorded 2026-11-14 | Replace with a lock-free open-addressing set if quarantine runs ever become multi-threaded hot paths; otherwise delete with the seed.

**Audited scope (2026-11-13):** `src/app/cli/native_build_*` + `worker_*` + `bootstrap_main.spl`, `src/compiler/80.driver/**`, `scripts/bootstrap/**`, plus the rows above for `src/app/bootstrap_builder/phase_admission.spl` and `src/app/build/{scheduler,clang_policy}`. **Not yet reviewed** (`file_lock` sites outside that scope; each needs its own row or an exit): `src/app/bootstrap_builder/{grouped_native_run,grouped_run}.spl` `manager.lock`, `native_group_linux_broker.spl` / `windows_group_broker.spl` `broker.lock` (timeout 0 = one try), `src/app/buildrunner/cli.spl` `manager.lock`, `src/app/release/{candidate_authority,session_authority}.spl`, `src/app/test_runner_new/{test_db_lock,test_runner_db}.spl`, `src/app/test_daemon/light_protocol.spl`, `src/app/spipe_knowledge_provider/lifecycle.spl`, `src/app/io/context_store_v1.spl`.

## 4. Correctness requirements

- **ABA:** every CAS cell that can recycle a value uses a version counter or a
  tag. A bare pointer compare is not enough when nodes are reused.
- **Progress:** lock-free is the baseline. Use wait-free where a real-time or
  kernel-adjacent path needs bounded steps per operation. State which guarantee
  the code provides.
- **Memory ordering:** publish with release and observe with acquire. Use
  relaxed ordering only for counters that publish nothing. Name the ordering
  at each atomic site.
- **Bounded retry:** CAS loops have a retry bound with backoff. Exhausting the
  bound returns a typed result. It never spins forever.
- **Panic-free (ADR-006):** a CAS failure is a typed retry/result
  (`Result`/`Option`, for example a `Contended` variant), never a panic.

## 5. Testing

- **Stress specs** run many writers against one cell or file and check for lost
  updates, torn reads, and duplicate or missing entries.
- **Interleaving tests** force the race windows (check-then-act,
  publish-then-read, ABA reuse) deterministically.
- **Every concurrency bug is P0.** Root-cause it, add a stress spec, and audit
  sibling claim/publish paths for the same shape.

## 6. Motivating case

The compiler/SCV refresh path previously serialized on shared mutable state and
locks. Its lockless redesign is the reference application of this document:
[`doc/05_design/compiler/scv/lockless_refresh.md`](../../../05_design/compiler/scv/lockless_refresh.md).

## 7. Relation to MDSOC+

For MDSOC+, cross-concern state is shared only as immutable snapshots. Concerns
communicate by CAS or by message passing, and locks live only at the
kernel/driver HAL boundary. See
[MDSOC+ § Concurrency](../../compiler/mdsoc/mdsoc_architecture_tobe.md#concurrency-lockless-by-default).
