# Source-based TLDR build v1 — per-file jobs, async readers, shared immutable AST

**Status:** AUTHORITATIVE design for the incremental compiler build (2026-10-24,
`release/1.0.0` @ `b4051cdeb1c`). It consolidates the user's 2026-10-24 design
decisions with the reviewed state of the code. Where it disagrees with
`semantic_incremental_build_cache_aop_formal_2026-08-09.md` or the 2026-10-08
research design, this document wins; those docs carry a superseded banner.
Execution order lives in
[`phase3_incremental_build_completion_2026-10-13.md`](../../../03_plan/compiler/phase3_incremental_build_completion_2026-10-13.md);
requirement history in
[`incremental_build_tldr_scv_implementation_2026-10-10.md`](../../../03_plan/compiler/incremental_build_tldr_scv_implementation_2026-10-10.md).
The additive semantic-cache work package (generic TLDR, AOP directory cache,
macro references) is
[`generic_aop_macro_semantic_cache_plan_2026-10-24.md`](../../../03_plan/compiler/cache/generic_aop_macro_semantic_cache_plan_2026-10-24.md).
Cache invalidation completeness, update-policy gaps and the Lean verification plan
(what is proved today vs. the live key) are in
[`cache_invalidation_formal_verification_2026-10-24.md`](cache_invalidation_formal_verification_2026-10-24.md).

Status words: **implemented** = landed on `release/1.0.0` with the cited
path:line and a live caller; **implemented, uncalled** = the module landed but
nothing in `src/` outside its own package calls it yet; **partial** = a piece
exists but the contract is not met; **planned** = no code yet. Line numbers are
at `b4051cdeb1c`, except rows marked (2026-10-24b), which are at `13ee5797f3c`
after #4367 #4370 #4372 #4373 #4378 #4379 #4382 landed.

## 1. Architecture rules (non-negotiable)

1. **Per-file jobs, no stage barrier.** Each source file is one job
   `src → parse → HIR → MIR → obj`; jobs run in parallel and never wait for a
   global parse-all / lower-all phase. Cross-module information comes only from
   TLDRs. (Motivation: batched whole-program HIR made Stage3 ~95 min with no
   object until the end.)
2. **Minimal or no locks; fully async.** Every I/O, cache read/write and every
   stage is an async task over immutable shared data. Publication is temp file +
   atomic rename; coordination is single-flight futures. No mutex, no file lock,
   no process lease in the compile path.
3. **Immutable shared data.** ASTs, TLDRs and cache cells are immutable once
   published; "empty" fields are set once (see §8).
4. **Content identity, never mtime.** Freshness is a content digest embedded in
   the artifact; branch/path/time are hints only.
5. **One reader interface** shared by the standalone compiler, `simple tldr`,
   the build runner and the test runner (§3).
6. **The parse cache entry IS the AST.** A parse-cache entry must be the final
   immutable binary AST, used in place (mmap or equivalent, no replay, no
   rebuild). A replay log — anything that has to be re-executed, re-bridged or
   re-assembled into node structures on every hit — is not a cache. (User rule,
   2026-10-24; today's flat-pool capture is non-compliant, see §4.) Packing layout, field inventory and clear/convert rules: [`packed_binary_ast_v1.md`](packed_binary_ast_v1.md). Landing review of the 2026-10-24 PRs against these rules, the corrected cache-limits spec and the Linux/portability layer: [`cache_build_review_and_portability_2026-10-24.md`](cache_build_review_and_portability_2026-10-24.md).
7. **Hash agility.** Different servers/caches may use different hash
   algorithms, at most three at once. Every persisted digest is
   `(algo_id, length, bytes)`, never a bare fixed-width field; a registry
   assigns ids and a security class (collision-resistant vs fast fingerprint);
   cross-host/remote identity uses a collision-resistant algorithm, fast ones
   only as local/in-memory indexes with full verification; readers advertise
   supported algorithms, producers write 1..3 digests, a hit needs a common
   algorithm that verifies; keys and paths are namespaced by algorithm; adding
   or removing an algorithm is schema-compatible; an unknown algorithm means
   the digest is absent (miss), never a match. Rules, registry, digest table
   and the audit of today's hard-coded `sha256`/`xxh3` sites:
   [`packed_binary_ast_v1.md`](packed_binary_ast_v1.md) §8. (User rule,
   2026-10-24.)

## 2. Per-file src→obj jobs (no stage barrier)

| Aspect | Design | Status |
|---|---|---|
| Job unit | one source file; stages are chained async tasks; the job's output is one object plus the module's refreshed TLDR | **partial** — #4348 (`1743475452d`) runs HIR/MIR *shard workers* inside the Stage3/4 capsule (`src/app/cli/native_build_main.spl` `native_build_focused_capsule_shards_v1`, ownership `src/compiler/80.driver/driver_hir_cache.spl` `hir_shard_owns`); #4368 (`fad47aafb67`) adds parse shards (`run_parse_shards_with_base`, cap `CAPSULE_PARSE_SHARD_DEFAULT_MAX = 8`, measured knee 8 workers → 103 s vs 1 → 459 s). Shards are still **phase-batched** (parse workers exit before surfaces; HIR then MIR), so the barrier remains. |
| Scheduler | the build runner (`src/app/buildrunner/runner.spl`, `src/lib/common/task_runner/{scheduler,journal}.spl`) admits one future per `(source digest, compiler identity, target)`; a job that needs another module's TLDR awaits that module's TLDR future, not its object | **planned** — current scheduler has task IDs/journal but no per-file compile future |
| Stage barriers to remove | `src/app/bootstrap_builder/phase_admission.spl:530-635` (`managed_phase_barrier_*`); parse-then-surfaces split in `src/compiler/80.driver/driver_source_pipeline_parsing.spl` | **planned** (replace with dependency-only joins) |
| Standalone mode | `simple compile` runs the same job graph in-process with `FileReader`; no daemon/SCV/Git launch required | **partial** — `FileReader` exists (§3); in-process job graph does not |

## 3. Reader interface

```
trait SourceReader:
    fn read_src(path)    -> ParserModule?   # full AST (cache hit or parse+store)
    fn read_tldr(path)   -> text            # "" when absent or stale
    fn update_src(path)  -> bool            # make the cached AST current
    fn update_tldr(path) -> text            # one parse fills AST cache + TLDR
```

| Aspect | Design | Status |
|---|---|---|
| Trait | as above; callers depend only on the trait | **implemented** — #4360 (`5bc6a2374c5`) `src/compiler/80.driver/cache/source_reader_v1.spl:28-32` (`trait SourceReader`), consumer `src/app/cli/tldr_entry.spl` |
| `FileReader` | direct file + private/shared parse-cache implementation | **implemented** — `source_reader_v1.spl:34-58` (`FileReader`, `file_source_reader_v1`) over `src/compiler/10.frontend/frontend.spl:115` (`frontend_parse_or_restore`) and `module_artifacts_v1.spl:165` |
| `CacheReader` | daemon/build-runner-backed implementation: returns the AST from the shared binary cache or **fails**; the compiler then parses and hands the AST back through `update_src`/`update_tldr`; a `FileReader` may no-op on `update_*` when the file is already current | **implemented, uncalled** (2026-10-24b) — #4370 (`f1f60b72c72`) `src/compiler/80.driver/cache/reader/cache_reader_v1.spl:25-54` (`trait CacheBlobPortV1` over `CacheGatewayAdapterV1`, `cache_reader_read_v1` gated by `CacheDaemonLifecycle`, blob kinds `simple.module.flat-pool-ast.v1` / `simple.module.tldr-companion.v4`). Zero callers in `src/`; it does not yet implement `SourceReader`, and no compile path constructs it |
| Async signatures | both readers return futures (`src/lib/nogc_async_mut/async/{future,promise,io}.spl`); the sync trait above is the v1 shape and must grow `-> Future<...>` without a second trait | **planned** — v1 trait is synchronous; the Windows "synchronous native parse lease" (kernel mutex) explored in the 10-10 plan is **dropped**, not landed |
| Miss path | `read_tldr` miss → `read_src` (parse) → build TLDR → `update_tldr` publishes atomically | **implemented** — `module_artifacts_v1.spl:165-182` (`module_artifacts_emit_v1`): freshness `:110` (`module_tldr_companion_fresh_v1`, embedded source sha256), publish `:150` |

## 4. One parse → full AST + TLDR

| Aspect | Design | Status |
|---|---|---|
| Single parse | `parse_full_frontend` fills the private parse cache and (opt-in) the shared parse CAS, and the same `ParserModule` feeds the TLDR | **implemented** — #4352 (`e237a8f6116`) producer; #4355 (`5e1503446f9`) AST-derived sections (`cache/module_tldr_ast_sections_v1.spl`); #4362 (`5df0df889f6`) `cache/module_public_summary_facts_v1.spl` turns the parsed module into `FrozenPublicFactV1` facts rendered by `10.frontend/cache_artifact/public_summary_projector.spl` (`module_artifacts_v1.spl:117-148`) — the earlier text-only extractor is gone |
| TLDR content (v4) | `summary` section = view of `PublicSummaryV1`; `generic`/`inline` body sections; `sif:` text; header `simple-tldr-companion: 4` | **implemented** — #4354 (`49ea04c8a54`) + #4355; `module_artifacts_v1.spl:50,71-109` |
| Parser spans/attrs | struct/class spans built from the declaration (`_FlatAstBridge/module_assembly.spl`); `inline` kept on function attributes (`core/_ParserDecls/enum_module_body.spl`) | **implemented** — #4371 (`616afdec054`); remaining line-0 spans on enums/traits/aliases/consts are named in `module_tldr_ast_sections_v1.spl` |
| `.tldr` ownership | compiler-written, non-importable companion of `PublicSummaryV1`, under an explicit `--out` root; never shadows a source, never replaces the package `.tld` / `PackageTldrHeaderV1` | **implemented** — decided in `doc/04_architecture/compiler_semantic_cache_manager.md` items 10-12 (#4366 `a5bb914ffcd`) |
| **Parse cache entry = final binary AST, used in place** (rule 6) | the cached bytes are the immutable AST that the compiler reads directly (mmap / zero-copy view); a hit performs no decode-into-pools, no bridge pass and no node re-assembly | **non-compliant today** (2026-10-24b) — the private and shared parse caches store the flat-pool **capture** (`src/compiler/10.frontend/core/flat_pool_codec.spl:1-22`: "a cache hit restores the pools verbatim and then runs the existing bridge (`flat_ast_to_module`) to rebuild the identical `ParserModule`"); the hit path `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1444` (`build_module_from_flat_pool_blob`) does `reset_all_pools()` → decode → bridge, i.e. a **replay/rebuild**, and the capture arm/record/take globals (`:1407-1428`) are mutable process state. Measured 2026-08-21 the bridge is 1-4% of parse cost, which is why it was accepted; under rule 6 it is a replay log, not a cache. **Required change:** make the flat-pool blob (or a successor layout) the in-place AST representation the frontend consumes, with set-once fields (§8) for resolution results, so a hit is a map + digest check only |
| HIR cache decode diagnostics | a refused HIR cache hit names the failing field | **implemented** (2026-10-24b) — #4379 (`47bd123bf37`) `src/compiler/20.hir/hir_codec.spl` `hir_module_decode_reason`, surfaced in `driver_hir_cache.spl` as `reason=decode … cause=…` |
| Seed bug records | `public_summary_projector_cannot_order`, `…missing_rt_io_file_open_read` | **recorded** — #4367 (`4d1b28ea510`), `doc/08_tracking/bug/*_2026-10-24.md` |

## 5. Publication: temp file + atomic rename

| Site | Status |
|---|---|
| `.tldr` companion: temp in the destination directory, `rt_file_rename` over (MoveFileExW REPLACE_EXISTING / rename(2)) | **implemented** — `module_artifacts_v1.spl:150-163` (`module_artifact_publish_atomic_v1`); temp name must be `{pid}.{xxh3(content)}` (pure) — the counter `_module_artifact_tmp_seq_v1` (`:52`) is a residual global and is to be removed |
| MIR cache entries + incremental manifest | **implemented** — #4364 (`12a39ae9dc4`) `src/compiler/80.driver/driver_build/incremental.spl:600` (`incremental_file_write_text`, temp = `{path}.{pid}.{xxh3_128(content)}.tmp`) |
| Private parse cache | **implemented** — `src/compiler/10.frontend/frontend_parse_cache.spl:177-188` |
| Shared parse CAS | **implemented** — `src/compiler/10.frontend/frontend_shared_parse_cas_v1.spl:5` ("immutable no-replace publish with a verified payload digest") |
| Rule | identical bytes for the same key make last-rename-wins harmless; **different** bytes for the same key are a producer nondeterminism fault: quarantine, never newest-wins | design rule |

## 6. Single-flight

| Aspect | Design | Status |
|---|---|---|
| Contract | the first request for a key creates a future and runs the work; later requests for the same key await that future and receive its result (success or failure); an abandoned future is re-driven by the next requester — no lease, no owner-death protocol | design |
| Test daemon | `src/app/test_daemon/daemon.spl:153-161` — `active_requests[hash_text(test_path)]`, later callers get `TRESP_QUEUED` + `redirect` | **implemented** (results, not ASTs) |
| Compiler / cache reader | per-key future table in the daemon and in-process in the standalone compiler | **implemented, uncalled** (2026-10-24b) — #4372 (`710cb72288c`) `src/compiler/80.driver/cache/daemon/cache_single_flight_v1.spl` (`cache_single_flight_key_v1(kind, digest)`, leader/waiter roles `SINGLE_FLIGHT_LEADER_V1`/`_WAITER_V1`) wired into `cache/daemon/cache_daemon_main.spl` (host admission + daemon ops). The compile path never reaches it: `CacheReader` has no caller, so today N concurrent producers still all parse and publish identical bytes (`module_artifacts_v1.spl:21-31`) |
| TLDR pointer fill (§7) | dereferencing an unset cross-module pointer goes through the same single-flight table | **planned** |

## 7. TLDR as forward declaration; lazy async pointers; shared TLDR table

- A TLDR is a **forward declaration**. Loading one never eagerly loads the TLDRs
  it references.
- A cross-module reference inside a TLDR is an **uninitialised async pointer**
  `(module id, decl id)`. Dereference asks the reader (`CacheReader` /
  `FileReader`) to fill it via single-flight; the pointer is then **set once**
  and never changes.
- Loaded TLDR ASTs live in one **shared immutable table** keyed by
  `(module id, TLDR content digest)`; an importer references the already-loaded
  entry directly and never re-reads the file.

| Piece | Status |
|---|---|
| Forward-declaration semantics in the companion (declarations only; generic/inline bodies as separate sections) | **implemented** — `module_tldr_ast_sections_v1.spl`, `module_public_summary_facts_v1.spl` |
| HIR consumer reading the companion instead of the source | **planned** — named gap in `module_artifacts_v1.spl:30-31` and phase3 "TLDR as imported header" |
| Async set-once pointers; shared TLDR table | **planned** — no once-cell primitive exists in `src/lib/nogc_async_mut/async/` yet; add `set_once` on `promise.spl` |

## 8. AST: set-once fields, adaptive attribute storage, shared immutable data

| Aspect | Design | Status |
|---|---|---|
| Immutability | the flat-pool AST blob is immutable; cache cells are no-replace | **implemented** — `frontend_shared_parse_cas_v1.spl:5`, `flat_pool_codec.spl` |
| Set-once fields | a field that is empty at construction may be assigned exactly once (lazy resolution results, pointer fills); a second assignment is a fault | **planned** |
| Attribute storage | per attribute kind, choose dense array vs hash side-table by measured usage frequency (hot = dense indexed by node id; rare = sparse map); the `collection_feedback` profile hook supplies the frequencies | **planned** — `src/compiler/10.frontend/core/collection_feedback.spl` is a profile hook only; see `doc/05_design/compiler/profile_switchable_container_algorithms.md` |
| Sharing | compilers, LSP, lint and the test runner map the same binary blob; nobody reparses | **partial** — shared CAS exists, opt-in via `SIMPLE_SHARED_PARSE_CAS_ROOT`; LSP/lint not wired; and the shared blob is a replay capture, not an in-place AST (rule 6, §4) |

## 9. In-memory id scopes (never persisted)

- Key: `xxh3_128` (`src/lib/common/crypto/xxh3.spl`; used at
  `frontend.spl:131,208`, `frontend_parse_cache.spl:126`,
  `incremental.spl:600`).
- Ids are **grouped by base file**: a per-file id is the 128-bit key truncated
  to **32 bits**; a local (intra-declaration) id to **16 bits**; a global id
  keeps 128 bits.
- Each scope carries a **bloom filter** over its truncated ids. A positive
  membership answer is verified against the full 128-bit key; on a verified
  collision the scope falls back to 128-bit ids for that entry. (Birthday bound:
  ~300 ids per 16-bit scope, ~65k per 32-bit scope before a collision is
  likely; the bloom filter detects, the fallback resolves.)
- **Never persisted**: cross-host/shared artifacts carry only full digests
  (phase3 rule "cross-host serialization excludes process-local IDs").

Status: **implemented, uncalled** (2026-10-24b) — #4373 (`d91c82221c7`)
`src/compiler/80.driver/cache/id_scope_v1.spl` (`id_scope_truncate_v1(full_key,
bits)`, 65,536-bit bloom, `id_scope_global_v1` 32-bit / `id_scope_file_v1` 16-bit
/ `id_scope_local_v1` 16-bit). Zero callers in `src/`: the frontend still mints
no truncated ids, so nothing is persisted either. **Deviation to fix:** the
module's per-file scope is 16-bit and global is 32-bit, while this design (and
the user) assign 32 bits to the per-file scope and keep the global scope at the
full 128-bit key; align the constants before the first caller lands.

## 10. Test-runner route policy

| Aspect | Design | Status |
|---|---|---|
| Cache checker keyed by file name | `hash_text(test_path)` keys both dedup and result cache | **implemented** — `test_daemon/daemon.spl:154`, `test_daemon/cache.spl:4` (`TestResultCache`) |
| Route policy | when a compiler connects, the runner routes its `read_*` by policy: **local** (answer from its binary AST cache), **redirect** (to the daemon owning the file's generation), **reroute-on-environment-change** (existing marker) | **partial** — only `src/app/test_daemon/light_protocol.spl:14-24` (`TEST_DAEMON_REROUTE_ENVIRONMENT`) exists |
| Runner-side TLDR refresh | the runner keeps src → TLDR current for the sources a spec touches, through the same producer | **implemented (opt-in)** — `src/app/test_runner_new/test_runner_single.spl:1185` (`_refresh_tldr_companions`, `SIMPLE_TLDR_ROOT`), spawning `simple tldr` |

## 11. Incremental rules

1. Recompile only: **changed sources**, their **TLDRs**, and the
   **aspect-affected pointcut set** (modules whose join points match a changed
   pointcut/advice — see the generic/AOP/macro plan §5).
2. **No relink** when every object hash is unchanged: emit no object, skip the
   link, and place the cached lib/dynlib/binary.
3. Freshness is content: source sha256 in the `.tldr`; xxh3_128 keys for caches;
   target/compiler identity in the key (`native_build_environment_identity.spl`).

Status: 1 — **partial** (TLDR regenerate on stale: implemented; pointcut set:
planned — `pointcut` appears only in `cache/schema/cache_protocol.sdn`);
2 — **planned** (no object-hash-equal link skip in `native_build_main.spl` or
`incremental.spl`).

## 12. Cache limits

| Limit | Meaning | Status |
|---|---|---|
| memory max | resident AST/TLDR table bytes; eviction only recomputes | **implemented, uncalled** (2026-10-24b) — #4378 (`322dfce08c0`) `cache/metadata/cache_limits.spl` `CacheRetentionLimitsV1` via `cache_retention_limits_load_v1` (`DEFAULT_MEMORY_MAX_BYTES` 1 GiB; precedence `SIMPLE_CACHE_*` env → `scripts/setup/host-env.shs` host config → default) |
| storage max | bytes under the one cache root | **implemented** — `cache_limits.spl:12-45` (`SIMPLE_CACHE_MAX_BYTES`, 10 GiB default, watermarks); shared by `CacheRetentionLimitsV1` (#4378) |
| max main branches | number of main-line generations retained | **implemented, uncalled** (2026-10-24b) — #4378 `DEFAULT_MAX_BRANCHES = 4`, plus a configured kept-branch list |
| per-branch versions per source file | max cache entries kept per `(branch, source path)` — **not** a per-branch byte cap | **implemented, uncalled** (2026-10-24b) — #4378 `DEFAULT_VERSIONS_PER_SOURCE = 3`; eviction order in `cache/gc/cache_eviction_plan_v1.spl:55` (`cache_eviction_plan_v1`, newest-first per source, branch last-used) |
| over-limit behaviour | **reject** the new write (fail closed, recompute later), never queue | **implemented, uncalled** (2026-10-24b) — `cache_eviction_plan_v1.spl:159` (`cache_eviction_admit_write_v1`); recorded as `compiler_semantic_cache_manager.md` item 13. No GC or publish path calls the plan yet (only `cache_limits.spl` imports it) |

Cache root: one canonical root via `$SIMPLE_CACHE`
(`src/compiler/80.driver/cache/cache_root.spl:31-35`); per-lane
`build/bootstrap/native_cache/<lane>` is the bootstrap-only exception
(`per_lane_private_caches.md`). Shared-state writer: the daemon's
`CacheWriterV1` owns the shared CAS; `driver_build/incremental.spl` is a
workspace-local store (now atomic, #4364). Object reuse stays shadow-only
(`cache/integration/shadow_mode.spl:12`, `SIMPLE_CACHE_V2_SHADOW=1`) until
admitted.

## 13. No locks / fully async — removal list

| Site | Today | Replacement |
|---|---|---|
| `cache/shared_generation_store.spl:2,327,379,406` | `file_lock("authority.lock")` | content-keyed `file_create_excl` publish + immutable generation pins |
| `cache/lease/lease.spl`, `cache/hir_body_typecheck_lease_v1.spl`, `cache/gc/reader_pin_gc_guard.spl` | process leases via `rt_process_exists` | generation pins as immutable tombstones; GC reclaims only unreferenced generations |
| 10-10 plan "synchronous native parse lease" (Windows kernel mutex) | design only, not landed | **dropped**; single-flight futures (§6) |
| `frontend.spl:115-140`, `frontend_parse_cache.spl:138` | blocking reads inside parse | async io wrappers; parse as a task |
| `_FlatAstBridge/module_assembly.spl:1407-1428,1444` | flat-pool capture globals + replay/rebuild on every hit | in-place immutable AST blob (rule 6); no pool reset, no bridge on a hit |
| `module_artifacts_v1.spl:52` `_module_artifact_tmp_seq_v1` | global counter | `{pid}.{xxh3(content)}` temp names (as #4364 did) |
| `frontend_parse_cache.spl:59-77,203`, `frontend_shared_parse_cas_v1.spl:30-35`, `driver_hir_cache.spl:85-99,205,343,524` | global mutable counters/tables | per-task immutable context; counters as an append-only event log |
| `bootstrap_builder/phase_admission.spl:530-635` | phase barriers | dependency-only joins on futures |
| `test_daemon/daemon.spl:161,168` | mutable `active_requests` dict (single-threaded) | keep; value becomes a future handle |

## 14. NUMA locality (2 sockets)

- The scheduler pins a job's whole chain (parse → HIR → MIR → obj) to the socket
  that first touched its source bytes; the shared TLDR table is
  **replicated-read**: each socket keeps its own read-only mapping of hot TLDR
  blobs (immutable, so no coherence traffic), while publication goes to the one
  cache root.
- The 80-thread host (2 sockets) measured contention on the shared cache
  directory above 8 parse shards (#4368); per-socket worker groups with
  socket-local temp directories and one rename into the shared root remove that
  contention without a lock.
- Status: **planned** — no NUMA awareness exists in the compiler
  (`numa` matches only MIR enum files); `--threads` admission is in
  `native_build_main.spl` (#4320 macOS vm_stat probe).

## 15. Resolved conflicts (2026-10-24)

| Topic | Decision |
|---|---|
| Cache root | single `$SIMPLE_CACHE` root (`cache_root.spl`); AOP-formal `.simple/build-cache/` split superseded; per-lane is bootstrap-only |
| Shared-state writer | daemon `CacheWriterV1` for the shared CAS; workspace-local stores allowed (atomic) |
| Object reuse | shadow-only until admitted (both docs agree; wording clarified) |
| Over-limit | reject, never queue |
| `.tldr` owner | compiler-side `update_tldr` to an explicit `--out` root; non-importable companion of `PublicSummaryV1`; package `.tld` stays canonical |
| Sync parse lease | dropped in favour of single-flight futures |
| Who parses on a miss | the compiler (daemon is a storage service, not a worker pool) |
| Hashes | xxh3_128 for in-memory keys and private caches; sha256 for embedded source identity; truncated ids never leave memory |
| Parse cache representation (2026-10-24b) | the entry is the final immutable binary AST used in place; the flat-pool capture + bridge replay is non-compliant and is to be replaced, not tuned |
| Id scope widths (2026-10-24b) | per-file = 32 bits, local = 16 bits, global = full 128-bit key; `id_scope_v1.spl` constants (global 32 / file 16) are to be aligned before first use |
