# Simple: pseudo-immutable cache and asynchronous build architecture

**Design baseline:** 2026-10-26
**Status:** Final consolidated design proposal; not an implementation-completion claim.
**Scope:** Embedded compiler, optional BuildRunner, shared TaskRunner/TestRunner scheduling, source/TLDR cache, binary AST/HIR/MIR, OBJ/BIN/LIB/SMF, compact IDs, concurrent hash algorithms, and resource-aware fiber/process execution.
**Latest requirement incorporated:** HIR contains **optional OS information and optional CPU information**, with explicit target-compatibility semantics.

The data structures, file-layout identifiers, configuration keys, and APIs below are proposed contracts. They are not assertions that these exact names or switches already exist. Repository observations are separated from proposed changes. No native compiler, scheduler, or performance test was executed for this report.

All repository observations cite `origin/release/1.0.0` @ `9c97b3cdcea` (merge of #4905). Paths are repo-relative; `file.spl:N` is a line at that commit. Tags: **[OBS]** = observed in the tree, **[PROP]** = proposed.

## Executive decision

Use **one compilation engine, one cache protocol, and one shared scheduling core**. The embedded compiler works without an external build runner; BuildRunner supplies a managed provider around the same engine; TestRunner submits work through the same scheduling core without becoming a dependency of ordinary compilation.

The default compilation operation is **source → OBJ**, with a fused execution path through the required parsing, semantic, lowering, optimization, and code-generation work. It does not require saving and reloading every intermediate stage. Persisted source MIR is optional. TLDR AST/HIR/MIR and optional executable TLDR OBJ are independently reusable.

Use **pseudo-immutable data**: an immutable artifact payload plus write-once scalar, dense-array, and sparse-hash attribute slots. A missing field is data state, not a future allocation. Asynchronous work is scheduled only for a useful producer, dependency wait, file/cache access, external process, or sufficiently large independent CPU task.

Use **XXH3-128 for fast trusted lookup**, collision-safe local 16/32-bit IDs for references, and algorithm-tagged concurrent digest aliases. Use an admitted cryptographic digest for the normal persistent cache and all untrusted imports; a disposable trusted local-only mode may instead retain exact collision verification. Never use a truncated hash as an identity proof.

Check the requested final artifact first. An unchanged valid OBJ/BIN/LIB/SMF requires **no compilation or linking**. If the destination is missing, materialize the cached result. Only cache misses descend into intermediate compilation stages.

## Contents

1. Requirements and non-negotiable invariants
2. Repository observations and reuse points
3. Architecture and recursive compilation graph
4. Pseudo-immutable fields and attribute storage
5. Identity, XXH3, compact IDs, and concurrent hashes
6. Cache keys, snapshots, and precise invalidation
7. HIR with optional OS and CPU information
8. Binary AST/HIR/MIR format
9. Slot publication, waiting, cancellation, and recovery
10. Compiler/provider interface and default execution
11. Standalone and managed process sequences
12. Early input acquisition and output I/O
13. Shared fiber/process scheduling and resource budgets
14. TestRunner reuse without compiler coupling
15. TLDR precompiled cache sets and optional OBJ
16. OBJ/BIN/LIB/SMF caching and no-change builds
17. Memory lifetime, eviction, and storage compaction
18. Missing pieces identified by the research
19. Implementation plan and ownership
20. Acceptance tests and formal invariants
21. Performance measurement and observability
22. Proposed configuration and rollout
23. Research and repository references

## 1. Requirements and non-negotiable invariants

| ID | Requirement | Binding decision |
|---|---|---|
| R01 | Same compiler API with and without BuildRunner | Swap providers, not compiler implementations. |
| R02 | Default source-to-object compilation | `compile(source, options)` requests OBJ; intermediate stages are internal unless a TLDR/debug option asks for them. |
| R03 | One process per source file | A file's parse→HIR→MIR→obj runs in ONE process (like `cc1` per TU); no HIR-shard / MIR-shard children for one file. |
| R04 | Stages are async tasks inside that process | parse, HIR, MIR, objgen each return an async handle; stages of different files overlap. |
| R05 | One invoker interface | Fiber and process invokers implement the same trait; the compile task is written once against it. |
| R06 | Target-neutral HIR, target-selecting MIR | HIR keeps every `@cfg` arm with optional OS/CPU info; MIR selects the base target. Target identity lives in MIR/OBJ keys, never in the HIR key. |
| R07 | TLDR is a forward declaration | Cross-module refs are lazy async pointers `(module_id, decl_id)`, filled via single-flight, set once; referenced TLDRs are never eager-loaded. |
| R08 | Cache entries are directly usable | Packed binary AST/HIR/MIR, one contiguous mmap-aligned blob, pointers swizzled to offsets/stable IDs, read in place. No replay bridge. |
| R09 | Bounded cache | memory max, storage max, max main branches, per-branch per-source entry **count and size** on memory and on storage; daemon usage ledger enforces. |
| R10 | Hash agility | ≤3 algorithms coexist; every digest is algorithm-tagged; unknown algorithm = miss, never match. |
| R11 | Lock-free publication | temp file + atomic rename; single-flight futures; immutable shared data; minimal or no mutexes. |
| R12 | Memory model | `BuildSession` owns build data and frees at end (module scopes freed after object emit); bounded global dataset (count + bytes); refcounted shared data freed at zero. The native runtime has no GC. |
| R13 | Final-artifact-first no-change build | Valid OBJ/BIN/LIB/SMF ⇒ no compile, no link; missing destination ⇒ materialize from cache. |
| R14 | Complete invalidation | Changed sources, their TLDRs, the macro/aspect pointcut-affected set, and the further input sources listed in the #4407 design are all cache inputs. |
| R15 | Truncated hash is never identity | 16/32-bit IDs are handles guarded by a bloom filter; collision ⇒ full digest or a distinct ID. |

## 2. Repository observations and reuse points

Everything in this section is **[OBS]**. PR numbers are verified merge commits on the base branch.

| Area | What exists | Where | PR |
|---|---|---|---|
| Reader interface | `trait SourceReader { read_src, read_tldr, update_src, update_tldr }` + `FileReader` | `src/compiler/80.driver/cache/source_reader_v1.spl:28-40` | #4360 `5bc6a2374c5` |
| Cache blob port | `trait CacheBlobPortV1.get_blob(kind, digest, max_bytes)`; pin TTL 30 s; kinds `flat-pool-ast.v1`, `tldr-companion.v4` | `src/compiler/80.driver/cache/reader/cache_reader_v1.spl:20-40` | #4370 `f1f60b72c72` |
| Single-flight | `CacheSingleFlightV1` with `leader_of`, `result_of`, `inflight_count`; key `kind:digest` | `src/compiler/80.driver/cache/daemon/cache_single_flight_v1.spl:24-145` | #4372 `710cb72288c` |
| TLDR lazy table | `TldrHandleV1 { module_id, decl_id }`, `TldrTableV1.is_loaded` | `src/compiler/80.driver/cache/reader/tldr_table_v1.spl:25-51` | #4386 `b2420e7ec0d` |
| Hash agility | registry ids (`SHA256=1, BLAKE3=2, SHA3_256=3, XXH3_128=16, XXH3_64=17, CRC32=18`), `struct DigestV1 { algo_id, .. }`, "unknown ⇒ absent" rule in header | `src/compiler/00.common/cache_contract/hash_algorithm_registry_v1.spl:4-53`; `80.driver/cache/hash_digest_v1.spl:12-23` | #4421 `176e7162b1e` |
| Compact IDs | `ID_SCOPE_{GLOBAL,FILE,LOCAL}_BITS = 128/32/16`, `IdScopeV1` with a 65 536-bit two-slot bloom and `collisions` counter | `src/compiler/80.driver/cache/id_scope_v1.spl:16-81` | (with #4391 docs) |
| Atomic publish | `module_artifact_publish_atomic_v1(path, content)` | `src/compiler/80.driver/cache/module_artifacts_v1.spl:484` | #4364 `12a39ae9dc4` |
| Packed AST `.spab` | 64-B header, 32-B section entries, 64-B section alignment, pointer-free pools, string offsets table; magic `SPLARTF1` | `src/compiler/10.frontend/core/flat_pool_packed_v1.spl:1-77,905-909` | #4445 `2400d260405`, reader #4436 `387470fb5b3`, mmap view #4397 `dd689c4da9c` |
| Cache limits | `DEFAULT_MAX_BYTES` 10 GiB, `MEMORY_MAX` 1 GiB, `MAX_BRANCHES` 4, `VERSIONS_PER_SOURCE` 3, per-source disk 256 MiB / memory 64 MiB / 64 entries | `src/compiler/80.driver/cache/metadata/cache_limits.spl:12-93` | #4378 `322dfce08c0`, #4381 `048d042e69d` |
| Eviction + admit-before-plan | `cache_eviction_plan_v1`, `cache_eviction_admit_write_v1`, `cache_eviction_admit_entry_v1` | `src/compiler/80.driver/cache/gc/cache_eviction_plan_v1.spl:64-241` | #4506 `1859d0f69a8` |
| Daemon | `CacheDaemonHost`, `CacheDaemonAdmission`, connect state machine | `src/compiler/80.driver/cache/daemon/cache_daemon_main.spl:17-53`, `cache_daemon_transport.spl:15-21` | #4396 `92a9517a17e` |
| Fiber scheduler | `FiberSchedV1`, `fiber_sched_submit(est_bytes)`, `_fs_admit_head`, step = done/yield/park | `src/lib/common/task_runner/fiber_scheduler.spl:31-126` | #4410 `ec9687bda8e` |
| Async IO reactor | `FiberIoReactorV1.submit_{open,read,close}`, `fiber_io_ready/result/data`, `fiber_io_pump` | `src/lib/nogc_async_mut/fiber/io_reactor.spl:18-99` | #4417 `dc84da8ed9c`, IOCP #4430 `89b3d70bc10`, pinning #4423 `3108e978f5c` |
| Per-file worker | `--file-worker=i/n`, `SIMPLE_FILE_WORKERS`, receipt with `hir_start/hir_done/deps_ready/mir_done/obj_done`, `file_worker_overlap_proven_v1` | `src/compiler/80.driver/driver_build/native_file_worker_v1.spl:1-42,63-173`; gate `scripts/check/check-per-file-overlap-receipt.shs:1-12` | P-A..P-H #4588 #4592 #4653 #4683 #4696; pool size #4897 |
| Build session | `class BuildSession`, `build_session_end_reset_globals_v1`, `SessionEndPort`, `_sffi_session_rc_share` | `src/compiler/80.driver/session/build_session.spl:45-148`; design `doc/05_design/compiler/memory/build_session_memory_model_v1.md` | #4898 `11a339267e3` |
| Incremental planner | `IncrementalModuleV1`, `PointcutDirChangeV1`, `pointcut_affected_files_v1`, `incremental_rebuild_plan_v1`, generic-template change input | `src/compiler/80.driver/cache/incremental_rebuild_plan_v1.spl:23-166` | #4511 `f37c76ddaf4` |
| Link receipt | object-hash link receipt; `SmfValidationSnapshot`, `validate_smf_with_deps`, `check_freshness` | `src/compiler/80.driver/cache/cache_validator.spl:127-244` | #4356 `3093d83a292` |
| HIR cache key | `hir_cache_key(source_path, closure_digest, is_entry, library_mode)`; `hir_cache_closure_digest(surfaces)` — **no target component** | `src/compiler/80.driver/driver_hir_cache.spl:137,157` | — |
| Parser `@cfg` stripping | `_pp_current_os/_pp_current_arch`, `_pp_eval_condition`, `_pp_preprocess_conditionals` drop arms for the *build host* target; receipted variant `_pp_preprocess_conditionals_target_receipted_v1` | `src/compiler/10.frontend/core/parser_preprocessor.spl:25-28,252,388,724`; `frontend_target_cfg_receipt_v1.spl:5-59` | — |
| MIR cfg selector (slice 1) | `mir_cfg_select_arm(conditions, target: MirTargetContext, features)`; `struct MirTargetContext` | `src/compiler/50.mir/mir_cfg_select.spl:118`; `src/compiler/00.common/mir_target_context.spl:3`; plan `doc/03_plan/compiler/hir_target_neutral_mir_target_plan.md` | #4905 `9c97b3cdcea` |
| Lean models | `BuildCache.lean` (27 theorems), `SingleFlightV1`, `HashAgilityV1` (9), `EvictionV1` (5), `EarlyCutoffV1` (4), `PrelowerKeyV1`, `WeaveCallOnlyV1`, `ReverseReferenceV2`; `cache_identity/Theorems.lean`; `async_compile/AsyncCompile.lean` (3) | `src/verification/build_cache/src/*.lean`, `src/verification/cache_identity/src/`, `src/verification/async_compile/src/` | #4407 `f3fa73957e1` plan |
| Invalidation completeness | design listing ~12 further input sources | `doc/05_design/compiler/incremental_build/cache_invalidation_formal_verification_2026-10-24.md` | #4407 |

**Hazard [OBS]:** `hir_cache_key` (`driver_hir_cache.spl:157`) has no target field, while `parser_preprocessor.spl:25-28` evaluates `@cfg` against the build host and drops the non-matching arms before HIR. Two hosts with different OS/arch therefore produce different HIR under the same key. Interim fix A-1 (key fold, WA-tagged), final fix P-1 (§7).

**Note [OBS]:** `native_file_worker_v1.spl:41-42` says the per-file lane is opt-in (`SIMPLE_FILE_WORKERS=1`), while `doc/03_plan/compiler/cache/cache_perfile_plan_index_2026-10-25.md` row D says the default flipped on 2026-10-26. Re-read `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1` before relying on either.

## 3. Architecture and recursive compilation graph

**[PROP]** Three layers, one engine:

```
TestRunner ──┐
BuildRunner ─┼─► Scheduler core (fibers + processes, one Invoker trait)
Embedded CLI ┘        │
                      ▼
            CompileTask(file) ── parse ▶ HIR ▶ MIR ▶ obj   (async stages, one process)
                      │ needs TLDR(m)        ▲
                      ▼                      │ set-once lazy pointer
            Reader {file | cache | daemon} ──┘  single-flight
```

A compile is a **recursive graph**: `obj(f)` needs `mir(f)` needs `hir(f)` needs `ast(f)` + `tldr(d)` for each import `d`. `tldr(d)` is a forward declaration: resolving it needs only `ast(d)`'s public surface, never `hir(d)`. The graph is demand-driven: a node is evaluated only when a consumer awaits it; a stale `tldr(d)` is rebuilt by the first requester and published by atomic rename (`build-src-based-tldr` rule). No phase barrier exists anywhere in the graph; the proof obligation is `obj_done(A) < hir_start(B)` for some pair (`check-per-file-overlap-receipt.shs:7-9` [OBS]).

## 4. Pseudo-immutable fields and attribute storage

**[PROP]** Every cached node is `{ payload: immutable bytes, slots: write-once }`.

| Slot kind | Use when | Layout | Set rule |
|---|---|---|---|
| scalar | ≤1 value per node, hot | inline in node record | CAS from `unset` sentinel; second write is a bug (debug assert), not a wait |
| dense array | attribute present on ≥ ~50 % of nodes | `u32 offset` into a per-section array, parallel to node id | written once by the producing stage; absent = `0xFFFF_FFFF` |
| sparse hash | attribute on < ~50 % of nodes | open-addressing table `(node_id → value_offset)` per section | insert-only; no delete; rebuilt on publish |

"Missing" is data state: readers test `is_set` and never allocate a future. Promotion dense↔sparse happens only at publish time, by the producer, based on the observed fill ratio; readers see one shape per blob. **[OBS]** `#4386` landed a set-once TLDR table (`tldr_table_v1.spl:25-51`); the adaptive dense/sparse split (tracker item 6, "~30 %") is not in the tree.

## 5. Identity, XXH3, compact IDs, and concurrent hashes

**[OBS]** The registry already defines ids and the "unknown ⇒ absent" rule (`hash_algorithm_registry_v1.spl:9-11,19-25`); `DigestV1 { algo_id, .. }` (`:33`); `digest_v1_set_of_text(algo_ids, data)` computes several tags at once (`hash_digest_v1.spl:23`); theorems `unknown_id_absent`, `equal_requires_known`, `different_algo_never_equal` are proved (`HashAgilityV1.lean:59-70`).

**[PROP] Key record (in memory and on disk).** One record, payload stored once:

```
KeyRecordV2 {
  payload_ref:  u32            # offset/id of the single payload
  n_digests:    u8  (1..=3)    # R10: at most 3 concurrent algorithms
  digests[3]:   { algo_id: u16, len: u8, bytes: [u8; 32] }   # tagged aliases, fixed 35 B each
}
```

**Index.** Three open-addressing hash maps, one per admitted algorithm (`by_algo[algo_id] : digest_bytes → record_id`), each sized to the record count. A lookup by any tagged digest is one probe in its algorithm's map: **O(1), no payload duplication**. Adding an algorithm = adding a map and backfilling lazily (a record gains the new tag on its next hit or republish); removing one = dropping the map; records with an unknown `algo_id` tag are skipped, never matched (schema-compatible with `HashAgilityV1.lean:59-82`). A match requires the same `algo_id` and byte equality; XXH3-128 (id 16) is admitted for *trusted local* lookup only; SHA-256/BLAKE3/SHA3-256 (ids 1-3) are the admitted cross-host identity algorithms. The persisted form is the existing `(algo_id u16, len, bytes)` binary form of the registry header (`hash_algorithm_registry_v1.spl:5`).

**[PROP] Compact reference IDs.** A 16- or 32-bit ID is a *handle*, never identity (R15). **[OBS]** `id_scope_v1.spl:16-19` already defines 128/32/16-bit scopes and a 65 536-bit, two-slot bloom with an `owners` map and a `collisions` counter (`:36-74`). Proposed sizing and semantics:

| Scope | Width | Grouping | Bloom | Target FP |
|---|---|---|---|---|
| local | 16 bit | one function/decl body | 4 KiB (32 768 bits), k=2 | <1 % at ≤2 k ids |
| per-file | 32 bit | one base source file | 10 bits/entry, k=3 | ≈1 % |
| global | 128 bit | XXH3-128 full | none (full digest) | — |

Allocation: `short = truncate(xxh3_128(full_key), width)`; bloom-negative ⇒ insert and own; bloom-positive ⇒ consult the exact `owners` map: same full key ⇒ reuse, different ⇒ **allocate a distinct ID** (linear probe in the compact space) and record the full digest in a per-scope collision side table so dereference falls back to the full digest. Rebuild: the bloom and owners map are rebuilt from the section's id table on load (they are derived data, never authoritative). Eviction: a scope dies with its owning blob; no cross-blob compact IDs. Persistence: the `.spab` id-range section (`flat_pool_packed_v1.spl:4` §2.2) stores `(short_id, full_digest_ref)` pairs sorted by short id; the bloom itself is not persisted.

## 6. Cache keys, snapshots, and precise invalidation

**[PROP]** Keys are tagged-digest tuples over *consumer-visible* inputs (`EarlyCutoffV1.lean:44-61` [OBS]):

| Tier | Key inputs | Target in key? |
|---|---|---|
| AST (`.spab`) | source bytes digest, compiler identity, codec version | no |
| TLDR | AST key + public-surface digest | no |
| HIR | AST key, closure digest of imported TLDR surfaces, `is_entry`, `library_mode` (`driver_hir_cache.spl:157` [OBS]) — **plus the `@cfg` arm set is kept, so no target is needed once §7 lands** | no (R06) |
| MIR / generic instance | HIR key + `MirTargetContext` digest + feature set + concrete key | **yes** |
| OBJ | MIR key + backend + opt level + CPU/SIMD tier + lane scope | yes |
| LIB/BIN/SMF | ordered object digests + linker identity + link order + system libs | yes |

A snapshot is the set of input digests the producer actually read, recorded in the entry (`EarlyCutoffV1.lean:52` `early_cutoff_sound`). Invalidation inputs, beyond source bytes: imported TLDR surfaces, macro definitions and expansion inputs, aspect pointcut sets and advice bodies → woven bodies (`pointcut_affected_files_v1`, `incremental_rebuild_plan_v1.spl:90` [OBS]), generic template bodies (`:157-166`), and the ~12 further sources of the #4407 design (trait impl set, inline/const deps, CTFE environment, link order, linker version, system libraries, `src/lib` identity, debug paths, advice→weave edges, re-export chains, compiler identity, options hash). Every one is a tagged digest in the snapshot; a missing one is a miss.

## 7. HIR with optional OS and CPU information

**[OBS]** Slice 1 landed: `mir_cfg_select_arm(conditions, target, features)` (`mir_cfg_select.spl:118`) selects an arm from a `MirTargetContext` (`00.common/mir_target_context.spl:3`). The parser still strips arms for the host (`parser_preprocessor.spl:388`), so HIR today is host-specific and its key (`driver_hir_cache.spl:157`) does not say so.

**[PROP]** HIR node `CfgSelect { arms: [(condition, body)], os_hint: Option<Os>, cpu_hint: Option<Cpu>, strict: bool }`. Semantics:

- All arms are kept (R06). `os_hint`/`cpu_hint` are **optional** and advisory: when set, they record the narrowest target family under which the HIR was *validated* (e.g. typechecked), not the only target it can serve.
- **Compatibility:** a HIR entry is usable for target `T` iff `os_hint ∈ {None, T.os}` and `cpu_hint ∈ {None, cpu_family(T)}`. A `None` hint is compatible with every target. A mismatch is a MIR-time *miss*, never a silent reuse. `strict=true` additionally requires an exact hint match (used for baremetal/none).
- MIR lowering evaluates each `CfgSelect` once via `mir_cfg_select_arm` and lowers only the chosen arm; unchosen arms are dropped from MIR, so MIR/OBJ keys carry the target (§6).
- Preprocessor: `_pp_preprocess_conditionals` becomes arm-*marking* instead of arm-*dropping*; the receipted variant (`:724`) already exists and is the hook.

## 8. Binary AST/HIR/MIR format

**[OBS]** `.spab` v1: 64-B header (`header_bytes`, `section_entry_bytes`, `flags`, `section_count`, `section_table_offset`, `blob_bytes`), 32-B section entries `(id, encoding, checksum_algo, offset, length, checksum)`, sections 64-B aligned and sorted by id, string pool as `offsets u32[n+1]` + raw UTF-8, element kinds i64/u8/str_index/offset (`flat_pool_packed_v1.spl:6-38`). Checksums are corruption-only, never identity (`:17`).

**[PROP]** Extend the same container to HIR (`.sphb`) and instance MIR (`.spmb`) with new section families; keep one codec. Rules: every in-memory pointer is swizzled to `(section_id, index)` or to a stable `(module_key_digest, decl_id)` before write; lazy pointers are written **unfilled** and refilled on first dereference via the reader (R07); readers map the blob and index it in place — there is no decode pass and no replay of a `ParserModule` capture (R08; tracker item 17). The section table doubles as the slot directory of §4: scalar slots live in the node array, dense arrays and sparse hashes are their own sections.

## 9. Slot publication, waiting, cancellation, and recovery

**[PROP]** A slot is published exactly once: producer writes `<path>.tmp.<pid>.<nonce>` then `rename` (`module_artifact_publish_atomic_v1`, `module_artifacts_v1.spl:484` [OBS]). In memory the same slot is a single-flight future: the first requester becomes leader (`CacheSingleFlightV1.leader_of`, `cache_single_flight_v1.spl:84` [OBS]); later requesters park (`fiber_step_park`, `fiber_scheduler.spl:41` [OBS]) and are woken by the publication, not by polling. **Cancellation:** a parked waiter may abandon; the leader never cancels a publication once the temp file is complete. **Recovery:** a leader that dies leaves only a temp file, which the daemon's tmp sweep removes after `DEFAULT_TMP_HOURS` (`cache_limits.spl:17` [OBS]); the next requester becomes leader (`claim_preserves_singleflight`, `timeout_without_death_cannot_reclaim`, `BuildCache.lean:96,120` [OBS]). The Fable P0 "waiters never woken" (tracker) is closed by requiring wake-on-publish in the daemon loop (step S1-5).

## 10. Compiler/provider interface and default execution

**[PROP]**

```
trait CompileInvoker:                      # R05 — one interface, two impls
    fn spawn(task: CompileTask) -> Handle  # FiberInvoker | ProcessInvoker
    fn await(h: Handle) -> CompileResult
    fn cancel(h: Handle)

struct CompileTask { source: SourceRef, target: MirTargetContext, want: Want(OBJ|TLDR|SMF),
                     reader: ReaderPort, session: SessionRef }

fn compile(task) -> Future<CompileResult>:          # written once, runs under either invoker
    ast  = reader.read_src(task.source)             # async
    tldr = ast.then(build_tldr)                     # publishes TLDR if stale
    hir  = (ast, imports(ast).map(reader.read_tldr)).then(lower_hir)   # lazy ptrs, no eager TLDR load
    mir  = hir.then(|h| lower_mir(h, task.target))
    obj  = mir.then(emit_object)
```

**[OBS]** The current entry points are synchronous (`compile_file`, `compile_files`, `compile_to_smf`, `driver_api_compile_single.spl:32-54`); the file-worker role is process-only (`native_file_worker_v1.spl:97-116`). The provider layer (BuildRunner) wraps the same `compile`: it adds the daemon reader, budgets, and receipts, and nothing else (R01).

## 11. Standalone and managed process sequences

**Standalone (embedded CLI):** `compile(f)` → `FileReader` (`source_reader_v1.spl:34` [OBS]) → stale TLDR rebuilt locally → OBJ written → done. No daemon, no runner.

**Managed (BuildRunner):** runner opens one `BuildSession`; scheduler admits `CompileTask(f)` per file under the memory budget (`fiber_sched_submit(est_bytes)`, `fiber_scheduler.spl:76` [OBS]); `ProcessInvoker` is chosen when `est_bytes` exceeds the in-process budget or the task needs isolation (memory is only returned to the OS by process exit — tracker 2026-10-25 note), otherwise `FiberInvoker`; results arrive as receipts (`native_file_worker_receipt_parse_v1`, `native_file_worker_v1.spl:146` [OBS]); final link runs once all objects are published or found valid (§16).

## 12. Early input acquisition and output I/O

**[PROP]** The scheduler issues `read_src`/`read_tldr` for the *next* admitted files while current ones lower, through the async reactor (`fiber_io_submit_read`, `io_reactor.spl:52` [OBS]); a fiber that would block on IO parks instead. Output: objects and blobs are written to the temp path through the same reactor and renamed on completion. Reads of published blobs use the mmap view (`#4397`); the mmap *writer* for objects and blobs (tracker item 27) is a gap.

## 13. Shared fiber/process scheduling and resource budgets

**[OBS]** `FiberSchedV1` has per-worker queues keyed by socket, a byte budget and `_fs_admit_head` admission (`fiber_scheduler.spl:45-126`); topology pinning across both processor groups landed in #4423; `check-per-file-overlap-receipt.shs` is the overlap proof.

**[PROP]** Budgets: `max_inflight_bytes` (sum of `est_bytes` of admitted tasks), `max_procs` (default host CPUs, `native_file_worker_pool_request_v1`, `native_file_worker_v1.spl:71` [OBS]), per-socket queues so a file's stages stay on one socket. Admission is the only backpressure; no stage barrier. `est_bytes` is learned per file from the previous receipt and defaults to 4× source bytes.

## 14. TestRunner reuse without compiler coupling

**[PROP]** TestRunner submits `CompileTask`s and test-execution tasks to the same scheduler core and reads the same cache through the daemon reader; the compiler never imports TestRunner. Route policy (tracker item 22, "not started") decides per file whether a TLDR refresh is served from cache or recomputed; the AST blob keyed by content digest + compiler identity is shared with LSP and lint so nobody reparses.

## 15. TLDR precompiled cache sets and optional OBJ

**[PROP]** Persisted per source: packed AST + TLDR companion (`CACHE_READER_KIND_*`, `cache_reader_v1.spl:21-22` [OBS]). A "TLDR set" for a package is the list of `(module_key, tldr_digest)`; a consumer loads entries on dereference only (R07). Optional executable TLDR OBJ: a precompiled object for the TLDR's inline/const bodies, keyed like OBJ (§6), used by consumers that never lower the module themselves. HIR stays in memory per job; no general MIR cache; instance MIR only per concrete key (plan index row 1 [OBS]).

## 16. OBJ/BIN/LIB/SMF caching and no-change builds

**[PROP]** Order of checks for `build(target_artifact)`: (1) destination exists and its recorded input snapshot verifies (`SmfValidationSnapshot`, `validate_smf_with_deps`, `cache_validator.spl:134-244` [OBS]) ⇒ **done, no compile, no link**; (2) destination missing but the cache has a blob under the same key ⇒ copy/hardlink it into place, done; (3) otherwise plan per-object: an object whose MIR key is unchanged is reused; if *every* object digest is unchanged the link receipt (#4356 [OBS]) proves the existing BIN/LIB valid and no relink runs; else link once. Per-dynlib receipts (tracker item 15) extend this to DLL swap.

## 17. Memory lifetime, eviction, and storage compaction

**[OBS]** `BuildSession` with `end` reset of process globals (`build_session.spl:59,87`), RC share port (`:71`), design `build_session_memory_model_v1.md` §2-3; `EvictionV1.lean` proves `read_after_evict_same_or_miss`, `evict_no_fabrication`, `pinned_survive`, `root_closed_no_dangling` (`:50-96`).

**[PROP]** Three lifetimes (R12): T1 session heap — freed at `BuildSession.end`, with a per-module sub-scope freed right after the module's object is emitted; T2 refcounted shared data — TLDR tables, packed blobs, interned strings, freed at zero; T3 bounded global dataset — `max_entries` + `max_bytes`, LRU eviction, entries pinned while a session holds a reference (closes Fable P0 "eviction during use"). Because the native runtime has no GC, in-process eviction lowers RSS only through T1/T2 frees; the process invoker is the hard ceiling. Storage: the daemon ledger tracks bytes per `(branch, source, tier)`; eviction newest-first within caps (`cache_eviction_plan_v1.spl:44,64`), then compaction removes empty section files.

## 18. Missing pieces identified by the research

| # | Gap | Evidence | Closed by |
|---|---|---|---|
| G1 | HIR key lacks target while parser strips arms | §2 hazard | A-1 (interim), P-1 (final) |
| G2 | Stage results are synchronous; no async handles | `driver_api_compile_single.spl:32-54` | S1-1..S1-4 |
| G3 | Single-flight waiters not woken (P0) | tracker | S1-5 |
| G4 | No `CompileInvoker` trait; process-only worker | `native_file_worker_v1.spl:97-116` | S2-1..S2-3 |
| G5 | Dense/sparse slot promotion absent | item 6 ~30 % | S3-1..S3-3 |
| G6 | Replay bridge still the hit path for HIR | item 17 | S3-4 |
| G7 | Daemon usage ledger (bytes per branch/src/tier) missing | `grep ledger daemon/` empty | S3-5 |
| G8 | mmap writer for objects/blobs | item 27 | S3-6 |
| G9 | Multi-algorithm key record + per-algo index | §5 | S2-6 |
| G10 | Collision side table + bloom sizing for compact IDs | `id_scope_v1.spl:19` fixed 65 536 bits | S2-7 |
| G11 | ~12 invalidation inputs not in snapshot | #4407 design | S3-7 (one PR each) |
| G12 | Test-runner route policy | item 22 | S2-5 |
| G13 | No final-artifact precheck / materialize step; SMF/LIB receipts missing | impl plan D9 | B-1..B-3 |

## 19. Implementation plan and ownership

Order is mandated: **Step 1 async nodes + async IO → Step 2 one compiler interface + runner wrapper + one invoker (multi-algorithm key record and compact IDs alongside) → Step 3 pseudo-immutable storage.** Target-neutral HIR and the fused default flip follow Step 3; correctness fixes (Wave A/B) may land standalone at any time. Cache keys, formats and limits slot in only where a step needs them. This table is the detailed view of `doc/03_plan/compiler/cache/pseudo_immutable_cache_impl_plan.md` (#4906) §2/§4; its IDs are given in the *Plan id* column. Every PR is small, lands on `release/1.0.0`, keeps the default behaviour unless stated, and ships a spec. **Owner roles:** *Guide* = high model (Fable/Opus) writes the contract + reviews; *Impl* = lower model (Sonnet/Haiku) implements and runs specs.

| PR | Step | Plan id | Change | Default | Guide / Impl |
|---|---|---|---|---|---|
| A-1 | standalone | C1 | HIR key interim fold of every preprocessor cfg input (os, arch, cpu, features, `cfg_env` knobs) into `hir_cache_key`; tagged `WA(hir-target-neutral)`, removed by P-1 | — | Guide: key shape / Impl |
| A-2 | standalone | C2 | Untrusted-input digest gate: every cross-trust read verifies an admitted crypto digest; xxh3 hit is a hint | — | Guide / Impl |
| A-3 | standalone | C3 | Truncated-hash audit script + `must_check_gates.sdn` row + dispatch case | — | Impl |
| B-1..3 | standalone | N3, N1, N2 | SMF/LIB receipts; final-artifact precheck (0 compiles, 0 links on identical build); materialize from cache by temp+rename | — | Guide: §16 spec / Impl |
| S1-1 | 1 | step 1 | `Future<T>` + `FiberStepV1` adapter: `parse_async(src) -> Future<Ast>`; sync `compile_file` calls `.await()` | unchanged | Guide: trait shape / Impl |
| S1-2 | 1 | step 1 | `lower_hir_async`, `lower_mir_async`, `emit_object_async` return futures; stages chained inside one process | unchanged | Impl |
| S1-3 | 1 | step 1 | `SourceReader` gains async twins (`read_src_async`, `read_tldr_async`) over `FiberIoReactorV1` | sync kept | Guide: port boundary / Impl |
| S1-4 | 1 | step 1 | Blob/object writes go through the reactor + `publish_atomic` | unchanged | Impl |
| S1-5 | 1 | step 1 | Daemon wake-on-publish for parked single-flight waiters (P0) + T-SF1 re-run | — | Guide reviews proof / Impl |
| S1-6 | 1 | step 1 | Receipt gains per-stage `*_start_ms/*_done_ms`; overlap gate extended | — | Impl |
| S2-1 | 2 | step 2 | `trait CompileInvoker` + `FiberInvoker` (in-process); reuses the per-file lane's worker role, no parallel trait | — | Guide / Impl |
| S2-2 | 2 | step 2 | `ProcessInvoker` wrapping `--file-worker`; `compile(task)` written once | — | Impl |
| S2-3 | 2 | step 2 | BuildRunner provider = same `compile` + daemon reader + budgets; standalone CLI proven identical by differential spec | — | Guide: R01 spec / Impl |
| S2-4 | 2 | step 2 | Scheduler chooses invoker by `est_bytes` vs in-process budget; per-socket queues | opt-in | Impl |
| S2-5 | 2 | step 2 (was S1) | TestRunner route policy submits through the core (no compiler import) | — | Impl |
| S2-6 | 2 (alongside) | hash IDs | `KeyRecordV2` + per-algorithm O(1) index; lazy backfill; T-HA1 extended (§5) | — | Guide: layout §5 / Impl |
| S2-7 | 2 (alongside) | hash IDs (was S2) | Compact-ID collision side table + bloom sizing + rebuild-on-load (§5) | — | Impl |
| S3-1 | 3 | C4 | Write-once scalar slots with `unset` sentinel + debug double-write assert | — | Guide / Impl |
| S3-2 | 3 | C4 | Dense-array attribute sections in `.spab` | codec v+1 | Impl |
| S3-3 | 3 | C4 | Sparse-hash attribute sections + publish-time promotion | codec v+1 | Impl |
| S3-4 | 3 | C4 | HIR blob (`.sphb`) read in place; retire replay bridge | behind flag | Guide / Impl |
| S3-5 | 3 | D12 | Daemon usage ledger (bytes/entries per branch/src/tier) enforcing R09 | — | Impl |
| S3-6 | 3 | item 27 | mmap writer for objects and blobs | — | Impl |
| S3-7 | 3 | #4407 | One PR per missing invalidation input, each adds a snapshot field + Lean source binding | — | Guide: formal binding / Impl |
| P-1 | after 3 | C5 | Target-neutral HIR: preprocessor marks arms (receipted path) instead of dropping; `CfgSelect` node with OS/CPU hints (§7); MIR uses `mir_cfg_select_arm`; drop A-1's WA | behind `SIMPLE_HIR_TARGET_NEUTRAL=1` | Guide: semantics §7 / Impl |
| P-2 | after 3 | S3 | Flip defaults: fused src→OBJ per-file lane, target-neutral HIR, async reader — only after S1-6 overlap proof and §21 numbers | flips | Guide decides |

## 20. Acceptance tests and formal invariants

Specs (SSpec, `test/01_unit/compiler/driver/`), each bound to a Lean theorem where one exists (`scripts/check/check-cache-formal-source-binding.shs`, `check-cache-protocol-formal.shs` [OBS]):

| ID | Spec | Invariant / theorem |
|---|---|---|
| T-K1 | Same source with a cfg arm, two targets ⇒ distinct keys (after A-1); identical HIR blob under one key (after P-1) | key completeness; `newer_header_cannot_mask_change` `BuildCache.lean:42` |
| T-SF1 | N waiters on one key get the leader's result; leader death ⇒ new leader | `claim_preserves_singleflight :96`, `timeout_without_death_cannot_reclaim :120`, `SingleFlightV1.lean` |
| T-HA1 | Record with 3 tags hits by any; unknown tag never matches; dropping an algorithm keeps the others | `unknown_id_absent :59`, `equal_requires_known :67`, `different_algo_digest_ne :82` |
| T-ID1 | Forced 16-bit collision allocates a distinct ID and dereferences to the right full digest | R15; new `CacheIdentity/Theorems.lean` lemma `compact_id_not_identity` **[PROP]** |
| T-EV1 | Pinned entry survives eviction; evicted entry is miss, never stale data | `pinned_survive :85`, `read_after_evict_same_or_miss :50`, `evict_no_fabrication :80` |
| T-EC1 | Changing a non-consumer-visible byte does not rebuild consumers | `early_cutoff_sound :52`, `compared_change_blocks_cutoff :61` |
| T-NC1 | Valid OBJ/BIN ⇒ zero compiles, zero links, zero parses | `warm_nochange_has_no_parse_or_scan :201`, `completed_publication_blocks_rebuild :123` |
| T-OV1 | ∃ A,B: `obj_done(A) < hir_start(B)` | `check-per-file-overlap-receipt.shs`; `wait_pipeline_not_safe` `AsyncCompile.lean:31` bounds what may block |
| T-R01 | Standalone vs BuildRunner produce byte-identical objects for the same inputs | R01 differential |
| T-MEM1 | RSS after `BuildSession.end` returns to pre-session baseline ± 5 % in-process; module scope freed after obj | `build_session_memory_model_v1.md` §3 invariants |
| T-INV1..12 | One spec per #4407 input: mutate it, expect a miss | source bindings in `src/verification/cache_protocol/source_bindings.txt` |

## 21. Performance measurement and observability

Record binary identity with every number (`readlink -f bin/simple`). Measured on this host (2 sockets, 80 threads, Windows) and Linux.

| Metric | How | Target |
|---|---|---|
| Stage-3 wall, whole-program vs per-file lane | bootstrap receipts | per-file ≤ 0.5× whole-program (baseline ~95 min single-process, tracker) |
| Overlap | `check-per-file-overlap-receipt.shs` | PASS on every stage-3 run |
| Peak RSS per worker / total | receipt + OS counters | per-process ≤ budget; total ≤ `max_inflight_bytes`; stage-3 total < 9 GB (was 9-39 GB) |
| CPU busy %, busy CPUs across both groups, disk queue/MBps per phase | tracker item 31 script | CPU-bound verdict ≥ 85 % busy during lowering |
| Warm no-change build | time + syscall count | 0 parses, 0 compiles, 0 links; < 1 s for the compiler tree |
| Cache hit latency | `.spab`/`.sphb` map + first dereference | < 1 ms per blob; no decode pass |
| Key lookup | per-algo index probe | O(1), ≤ 3 probes per lookup regardless of tag count |
| Compact-ID collisions | `IdScopeV1.collisions` | < 1 % per scope, logged |
| Ledger | bytes/entries per branch/src/tier vs caps | never over cap; eviction count |

Observability: every receipt and ledger row is a `key=value` text line (receipt codec `native_file_worker_v1.spl:140`); the daemon exposes `inflight_count`, waiter count, ledger totals.

## 22. Proposed configuration and rollout

Keys **[PROP]** (env now, `simple.sdn` later): `SIMPLE_FILE_WORKERS` (exists), `SIMPLE_HIR_TARGET_NEUTRAL`, `SIMPLE_ASYNC_READER`, `SIMPLE_CACHE_ALGOS=xxh3-128,sha256[,blake3]` (≤3), `SIMPLE_CACHE_MEMORY_MAX`, `SIMPLE_CACHE_STORAGE_MAX`, `SIMPLE_CACHE_MAX_BRANCHES`, `SIMPLE_CACHE_PER_SRC_ENTRIES`, `SIMPLE_CACHE_PER_SRC_BYTES` (map onto `cache_limits.spl:88-93`), `SIMPLE_INFLIGHT_BYTES_MAX`. Rollout: each step lands opt-in; S3-10 flips a default only with the §20 specs green and §21 numbers recorded in `doc/10_metrics/`. Rollback is unsetting the flag; no on-disk migration is needed because unknown sections and unknown algorithm tags are skipped.

## 23. Research and repository references

- Plans: `doc/03_plan/compiler/cache/pseudo_immutable_cache_impl_plan.md` (+`_tldr.md`, #4906 — the PR-order authority this §19 details), `doc/03_plan/compiler/hir_target_neutral_mir_target_plan.md` (+`_tldr.md`), `doc/03_plan/compiler/cache/cache_perfile_plan_index_2026-10-25.md`, `doc/03_plan/compiler/cache/generic_aop_macro_semantic_cache_plan_2026-10-24.md`, `doc/03_plan/compiler/cache/semantic_incremental_build_v2_plan_2026-08-09.md`.
- Designs: `doc/05_design/compiler/memory/build_session_memory_model_v1.md`, `doc/05_design/compiler/incremental_build/cache_invalidation_formal_verification_2026-10-24.md` (#4407), `.../src_based_tldr_build_v1.md`, `.../true_per_file_pipeline_v1.md`, `.../build_runner_fiber_scheduler_v1.md`, `.../packed_binary_ast_v1.md`, `.../per_lane_private_caches.md`.
- Code: `src/compiler/80.driver/cache/{source_reader_v1,id_scope_v1,hash_digest_v1,incremental_rebuild_plan_v1,module_artifacts_v1,cache_validator}.spl`, `.../cache/reader/`, `.../cache/daemon/`, `.../cache/metadata/cache_limits.spl`, `.../cache/gc/cache_eviction_plan_v1.spl`, `.../driver_hir_cache.spl`, `.../driver_build/native_file_worker_v1.spl`, `.../session/build_session.spl`, `src/compiler/00.common/cache_contract/hash_algorithm_registry_v1.spl`, `src/compiler/00.common/mir_target_context.spl`, `src/compiler/50.mir/mir_cfg_select.spl`, `src/compiler/10.frontend/core/{parser_preprocessor,flat_pool_packed_v1}.spl`, `src/lib/common/task_runner/fiber_scheduler.spl`, `src/lib/nogc_async_mut/fiber/io_reactor.spl`.
- Proofs and gates: `src/verification/build_cache/src/*.lean`, `src/verification/cache_identity/`, `src/verification/async_compile/`, `scripts/check/check-per-file-overlap-receipt.shs`, `check-cache-formal-source-binding.shs`, `check-cache-identity-formal-proofs.shs`, `check-cache-protocol-formal.shs`.
- PRs (verified merges on `release/1.0.0`): #4356 #4360 #4364 #4370 #4372 #4378 #4381 #4386 #4396 #4397 #4407 #4410 #4417 #4421 #4423 #4430 #4436 #4445 #4505 #4506 #4511 #4588 #4592 #4653 #4683 #4696 #4897 #4898 #4905.
