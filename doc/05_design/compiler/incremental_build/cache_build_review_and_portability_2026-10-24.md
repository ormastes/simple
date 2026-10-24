# Cache/build landing review and Linux + platform-independence plan — 2026-10-24

**Scope:** read-only review of what landed on `release/1.0.0` @ `dd689c4da9c`
for the cache/build work (#4348 #4352 #4354 #4355 #4360 #4361 #4362 #4364
#4365 #4366 #4368 #4369 #4370 #4371 #4372 #4373 #4375 #4378 #4379 #4380 #4381
#4383 #4386 #4387 #4388 #4389 #4390 #4391 #4392 #4393 #4397; docs #4382
#4384; held #4356 link receipt), judged against
[`src_based_tldr_build_v1.md`](src_based_tldr_build_v1.md),
[`packed_binary_ast_v1.md`](packed_binary_ast_v1.md) and
[`generic_aop_macro_semantic_cache_plan_2026-10-24.md`](../../../03_plan/compiler/cache/generic_aop_macro_semantic_cache_plan_2026-10-24.md);
then how each piece behaves on Linux/macOS/FreeBSD, and one platform-neutral
layer so compiler/cache code carries no OS branches. Nothing was built or run;
line numbers are at `dd689c4da9c`.

**Headline:** the design surface landed as ~15 new modules, but **most are not
on the compile path yet** (0 live callers), the two mechanisms that *are* live
still violate the two central rules (stage barrier in the capsule shard
pre-pass; polling "futures" in single-flight), and the packed-blob view shipped
with a third container format. Nothing landed is unsafe for the Stage3/Stage4
build except the shared-directory claim contention (#4380) and the span byte
change (#4371), both named below.

## 0. This CPU platform first — correctness and efficiency (Windows, 2 sockets × 20c/40t, per-socket L3 + NUMA memory, C: nearly full SSD)

User priority: before anything else the cache must have **no bugs and no
efficiency problems on this host**. Everything below is read-only evidence at
`dd689c4da9c`; where a number could not be read from source, the benchmark
that produces it is named instead of guessed.

### 0.a Correctness

| Pri | Bug class | Evidence (path:line) | Impact on this host | Fix | Proof |
|---|---|---|---|---|---|
| **P0** | **Single-flight waiters never see completion.** `future()` returns `Future.pending()`; the "workaround" is that participants re-poll and the table is re-read on each poll (`cache_single_flight_v1.spl:9,24`; `cache_daemon_main.spl:135` "participants only poll", `:154 poll_artifact`). With 40 shard workers asking for the same TLDR, 39 poll loops burn cores and the IPC file queue until the leader writes. | #4372 `src/compiler/80.driver/cache/daemon/cache_single_flight_v1.spl`, `cache_daemon_main.spl:135,154` | wasted cores, cross-socket cache-line traffic on the flight table, latency = poll period | completer per flight; `complete()` resolves every waiter's future; no re-poll | spec: 1 leader + 39 waiters, assert each waiter is woken exactly once and total `poll` calls == waiters; benchmark: 40 same-key requests, p95 waiter latency ≤ leader time + 1 ms |
| **P0** | **Eviction during use.** `CacheEntryUseV1` has no pin/live-view field (`cache_eviction_plan_v1.spl:21-27`); the plan can evict an entry another process has mapped. On Windows the delete fails with a sharing violation unless the reader opened with `FILE_SHARE_DELETE` (then the view stays valid until unmap, which is the correct semantics); on a reader that opened without it, the daemon's eviction fails and the plan's `disk_bytes_after` is wrong. | #4378 `cache/gc/cache_eviction_plan_v1.spl:21-35,159` | wrong accounting → storage cap overshoot on a nearly-full C:; or EACCES storms | ledger open/close rows (§3.2) and never evict an entry with a live-view row; readers open with share-delete; eviction = rename to `trash/` first | spec: map entry, run plan, assert entry not in `evict`; fixture deleting a mapped file on Windows must be a rename, never an unlink failure |
| **P0** | **Stage barrier makes every shard wait for the slowest** (`native_build_main.spl:1208,1218,1233`). On 80 threads with the measured knee at 8 workers (103 s) this is the dominant wall-time term of Stage3. | #4348/#4368 | ~3× idle cores per phase; no overlap of parse/HIR/MIR across modules | per-module jobs (design §2) | benchmark: object-arrival timeline; first object before last parse ends |
| **P1** | **xxh3-128 key hit is not verified against the source.** Private cache key = `xxh3_128_text(content)` (`frontend_parse_cache.spl:126`); the entry's checksum is over the **blob** (`:168,175`), and `build_module_from_flat_pool_blob` never compares `parse_source` to anything (`module_assembly.spl:1444-1462`). A 128-bit collision is ~2⁻⁶⁴ per pair — negligible in practice, but it violates "fast fingerprint only with full verification" (packed §8.1 rule 2), and the same shape will be copied into the daemon key. | `src/compiler/10.frontend/frontend_parse_cache.spl:126,168,175` | silent wrong AST on collision; rule violation | store a collision-resistant source digest in the entry header (algo-tagged) and compare on hit | spec: two synthetic sources with a forced equal xxh3 key (test hook) → second must miss |
| **P1** | **Generation mix / torn reads are prevented only where temp+rename is used.** Verified: `.tldr` (`module_artifacts_v1.spl:205`), MIR/manifest (`incremental.spl:600`), parse caches. **Not** verified: `.rr` pointer temp is pid-only (`reverse_reference_receipt.spl:252`) → two writes in one process can interleave; `compiler_entry_closure_publish_v1` (#4387) unverified. | as cited | torn `.rr` pointer → wrong impact set on incremental | content in temp name; audit #4387 | spec: two publishes from one pid, same pointer path, assert both temps distinct and final bytes = one complete write |
| **P1** | **Stale hits after a *compiler* change.** Private cache header carries `FRONTEND_CACHE_ENTRY_VERSION + FLAT_POOL_CODEC_VERSION + scope` (`frontend_parse_cache.spl:~130`) — not the producer identity. A desugar/bridge change without a codec bump serves old blobs (this is why `spl-flatpool-v8-a5-refusal` had to be bumped by hand). | `frontend_parse_cache.spl` header fn | silent stale AST across compiler rebuilds in one day of 30 PRs | put `compiler_identity` (algo-tagged) in the key as the packed doc §7.1 does | spec: same source, two producer identities → two entries |
| **P1** | **Unknown-algorithm-as-match is not yet possible but is one `if` away.** No registry exists; every verify is `sha256_text(x) != digest` (14 sites, §1 #7). The first second-algorithm site that compares *lengths* instead of bytes will match. | packed §8.4 audit list | future false hit | `DigestV1` + registry; verify = (algo known) ∧ (bytes equal); unknown ⇒ absent | spec: digest table `{0x7FFF}` ⇒ miss; `{0x7FFF, sha256}` ⇒ verify via sha256 |
| **P1** | **Windows rename onto an open file.** `rt_file_rename` = `MoveFileExW(REPLACE_EXISTING)` (`runtime_native.c:16127-16134`); it **fails** when the destination is open without `FILE_SHARE_DELETE`. Readers today use `file_read`/`rt_file_read_regular_no_follow_bounded` (share mode unknown → check), so a producer republishing a `.tldr`/blob while 39 workers read it gets `false` from `module_artifact_publish_atomic_v1` and the compile proceeds without the refresh (silently stale companion on the next job). A loaded `.dll`/`.exe` can never be replaced. | `runtime_native.c:16127-16134`; `module_artifacts_v1.spl:205-214` | lost refresh under contention; dynlib outputs unreplaceable | open cache files with share-delete; publish dynlib/bin under versioned names + manifest switch | spec (Windows): reader holds file open, producer renames over it → success and reader still reads old bytes to EOF |
| **P1** | **`file_write_bytes` byte corruption (0x53→0x98).** Confirmed ABI mismatch: the compiled call lowered to the 3-argument raw `rt_file_write_bytes` with a packed-array handle where the authority exports the 2-argument tagged `rt_file_write_bytes_array` (`doc/08_tracking/bug/native_test_source_stage_bytes_corruption_2026-10-21.md` §Confirmed ABI cause). Any blob writer using `file_write_bytes` from a native-built compiler is at risk. | `src/lib/nogc_sync_mut/io_runtime.spl:342`; bug record | corrupt cache blobs written by the self-hosted compiler; validation (§4 of packed doc) catches it as a miss, but every write is wasted | land the tagged-facade fix; blob writers verify by re-reading + digest before rename (write-verify-rename) | spec: write 8192 pseudo-random bytes via the native binary, read back, byte-compare (the record's own probe) |
| **P1** | **HIR cache decode refusals (~10 % on windows-gnu).** Encoder writes a nil sentinel into a non-optional scalar and reports success; 231 generated decoder sites refuse that byte (`generated/hir_codec.spl:166-172`; `doc/08_tracking/bug/hir_codec_encodes_nil_non_optional_scalar_that_decode_refuses_2026-10-24.md`). The module is refused **forever**, so every build re-lowers it. #4379 only names the field. | `src/compiler/20.hir/generated/hir_codec.spl:166-172`; `driver_hir_cache.spl` (`reason=decode`) | permanent ~10 % HIR cache miss → full lowering each build | encoder must refuse (fail closed) what the decoder refuses, or the slot must be optional; add a producer-side self-decode before publish | spec: encode a module with nil in a non-optional scalar → encode returns error; corpus run: refusal rate 0 |
| **P2** | **Set-once violations:** none can exist yet — no set-once field or lazy pointer landed (`tldr_table_v1.spl`, `generic_tldr_view_table_v1.spl` have 0 callers). Guard before first use: a second assignment must panic in debug and be a fail-closed miss in release. | — | — | add `set_once` helper with a spec before the first consumer | spec: double-fill panics |
| **P2** | **Key collisions between shards.** Shard ownership = bare `xxh3_64(path)` with a sign-bit workaround for a windows-gnu `>>` codegen bug (`driver_parse_shard_hash.spl:15`). Correct today; the codegen bug is the real risk. | #4368 | wrong owner = duplicate parse (benign) | file + fix the `>>` bug; keep the workaround until then | existing spec `driver_parse_shard_hash_spec.spl` |

### 0.b Efficiency on 2 sockets / 80 threads

| Pri | Issue | Evidence | Impact | Fix | Measure |
|---|---|---|---|---|---|
| **P0** | **Processor groups.** Windows splits 80 logical CPUs into two groups (≤64 each); a process is scheduled in **one** group unless it opts in. `rt_cpu_count` is correct (`GetActiveProcessorCount(ALL_PROCESSOR_GROUPS)`, `src/runtime/platform/windows_system_processor_count.h:9`) so admission asks for 40 jobs, but **no code sets group affinity** (zero hits for `SetThreadGroupAffinity`/`GetLogicalProcessorInformationEx` in `src/runtime` and the seed). Shard **processes** are placed by the OS (fine, each new process may land in either group), but any **in-process** thread pool (daemon, future executor) is confined to one group = one socket. | `windows_system_processor_count.h:9`; absence of affinity APIs | daemon/executor use ≤40 threads on one socket; cross-group work needs explicit placement | layer `cpu_topology()` returning groups=NUMA nodes; `pin_thread(group, mask)`; worker pools = one per group | benchmark: thread pool of 80 workers → measure active CPUs per group via `GetThreadGroupAffinity`; expect both groups busy |
| **P0** | **8-worker knee is contention, not CPU.** 1→459 s, 8→103 s, 16→114 s, 40→211 s (`native_build_main.spl` comment at `CAPSULE_PARSE_SHARD_DEFAULT_MAX`). Causes visible in source: every worker repeats the ~25 s closure walk; all workers claim from one `queue_dir` via exclusive-create (`driver_source_pipeline_parsing.spl:230,237`); all workers write one cache directory; `MOVEFILE_WRITE_THROUGH` on every rename (`runtime_native.c:15068`) forces a flush per publish on an SSD that is nearly full (write amplification + free-space hunting). | as cited | 2.1× slowdown from 8→40 workers; 72 idle threads | publish closure once (#4387 direction); precomputed per-worker lists (no claim dir); per-socket temp dirs; drop `WRITE_THROUGH` from renames that are not durability points (fsync only the journal) | benchmark: parse shards at 8/16/40 with (a) claim dir removed, (b) write-through removed, (c) per-socket temp dirs; report wall, SSD write bytes, `queue_dir` op count |
| **P1** | **Cross-socket traffic on shared mutable tables.** `HeapRegistryShard.epoch: AtomicU64` with `fetch_add(AcqRel)` on every free and `Mutex<HeapPtrSet>` per shard (`heap.rs` #4375 delta: `HEAP_REGISTRY_SHARDS = 64`, `epoch.fetch_add`); shard choice is by address bits (`mixed >> 58`), so two sockets hammer the same 64 cache lines. Seed-only, but the seed runs Stage1/2. | `src/compiler_rust/runtime/src/value/heap.rs` (#4375) | false sharing + cross-socket atomics on every alloc/free | per-thread registries with epoch per thread; shard array padded to 64 B per shard | perf counter: `OFFCORE_RESPONSE` remote-DRAM hits during Stage2; or Rust microbench alloc/free on 80 threads pinned 40/40 |
| **P1** | **Shared immutable tables are fine *only if* they are truly immutable and replicated-read.** TLDR table (#4386 `tldr_table_v1.spl`), id scopes (#4373 `id_scope_v1.spl`, bloom `ID_SCOPE_BLOOM_BITS_V1 = 65536` = 8 KiB mutable bitset) and the single-flight table (#4372) are **mutable** structs updated on insert; once they get a caller, inserts from 40 workers on two sockets will bounce lines. | `cache/id_scope_v1.spl:18`, `cache/reader/tldr_table_v1.spl`, `cache/daemon/cache_single_flight_v1.spl` | write-sharing on the hot path | per-socket (per worker group) instances; publish-by-replace (immutable snapshot + atomic pointer swap), never in-place insert; bloom per scope per thread | microbench: 80 threads inserting into one vs per-socket tables |
| **P1** | **First-touch page placement of mmapped blobs.** `sosix_file_map` maps whole files; pages fault in on the socket of the first reader. With one daemon thread touching every blob (validation pass, §4 step 7 of the packed doc) all pages land on the daemon's socket; workers on the other socket pay remote DRAM for every node read. | `sosix/file_map.spl:34`; packed doc §4 | ~1.5-2× node-read latency for half the workers | validate in the **reader** (first touch = consumer); or map per socket (two views of the same file — page cache is shared, but user mappings are per process so this is naturally per worker process; the daemon must not pre-touch) | benchmark: time to iterate a 50 MB blob from a worker pinned to socket 1 after the daemon validated it on socket 0, vs validated locally |
| **P1** | **Daemon single-thread bottleneck + file-queue IPC.** The daemon host folds requests in one loop (`cache_daemon_main.spl`, "the daemon's single loop" in `cache_eviction_plan_v1.spl:19`); requests arrive as files; 40 workers × (poll loop from P0 above) = thousands of directory ops/s on the SSD. | as cited | daemon becomes the serial section; SSD metadata ops | daemon answers only misses/publishes; hits are served by the worker mapping the blob directly (content-addressed path, no round trip); waiters are woken, not polling | benchmark: 40 workers × 1000 hits: daemon CPU %, directory ops/s |
| **P1** | **Per-section verification cost on load.** Packed doc §4 step 5 hashes the whole body (xxh3 ~10 GB/s → 5 ms per 50 MB) or per-section lazily; today's text codec instead decodes everything (`module_assembly.spl:1444`) and then **re-encodes** for the sanitize check (`:1509-1512`) — two full passes plus allocation on every hit. | `module_assembly.spl:1444-1512` | hit cost ≈ 20-30 % of a parse (`PARSEHIT` profile line `:1500`) | packed view: one hash pass + bounds pass, no decode | `SIMPLE_PARSE_PHASE_PROFILE=1` already prints `PARSEHIT init/restore/bridge`; record before/after on the bootstrap closure |
| **P1** | **fsync / write-through on a nearly full SSD.** 12 fsync sites in `shared_generation_store.spl`, 6 in `cas_batch_transaction.spl`, 6 in `native_noop_admission.spl`; every `rt_file_rename` on Windows passes `MOVEFILE_WRITE_THROUGH` (`runtime_native.c:15068`). `min_free_ratio` (5 %) exists in `cache_limits.spl:15` and is read by `gc/admission.spl:109` but **no publish path calls admission** (0 callers of `cache_eviction_admit_write_v1`; `gc/admission` is only reached from GC). On a full C: the cache can fill the disk and every subsequent temp-file write fails after the parse was already done. | as cited | SSD write amplification; disk-full failure mode | fsync only the journal/receipt that defines durability; blobs rely on rename atomicity (crash ⇒ miss, by design); enforce `min_free_ratio` in the producer before writing the temp | benchmark: publish 1000 blobs with/without write-through, measure wall and `PhysicalDisk\Disk Write Bytes/sec`; spec: free space below min_free ⇒ publish rejected before the temp is created |
| **P2** | **Memory admission vs Windows working set.** `memory_max_bytes` counts mapped bytes (design §3.2); Windows charges mapped file pages to the process working set only when touched and trims under pressure; a 1 GiB cap on 80 workers is 80 GiB of potential mappings — fine for file-backed read-only pages (reclaimable) but the admission must not count them as committed memory, or it will refuse hits that cost nothing. | `cache_limits.spl:92` | false memory rejects, or none at all if uncounted | count **private** bytes (decoded side arrays, set-once overlays) against `memory_max_bytes`; mapped read-only bytes have their own soft cap | measure: `Process\Working Set - Private` vs `Working Set` of a worker with 50 blobs mapped |
| **P2** | **False sharing in parallel-array pools.** `_Thread_local` transient globals (`runtime_memory.c:48-51`) are per thread — good; but the frontend pools are process globals written by one parser thread, so only the shard-worker (multi-process) model avoids sharing. Any in-process parallel parse would share the pool globals. | `runtime_memory.c:48-51`; `core/types.spl` pools | blocks in-process parallelism | keep multi-process until pools are per-job | — |

**Measure first (read-only is exhausted):** the knee decomposition (claim dir / write-through / closure walk), the daemon-touch vs reader-touch mmap latency, and the processor-group occupancy are the three benchmarks to run before any further cache PR lands.

## 1. Findings, ranked

### P0

| # | Finding | PR | path:line | Rule | Fix |
|---|---|---|---|---|---|
| 1 | **Stage barrier is still there.** The capsule pre-pass runs parse for every module, waits for all parse workers, then runs `hir-shard` for every module, waits, then MIR. | #4348 #4368 | `src/app/cli/native_build_main.spl:1208` (`run_parse_shards_with_base` blocks), `:1218` (`run_ledger_shards("hir-shard")`), `:1233` (MIR phase) | per-file jobs, no stage barrier (design §2) | one worker pool per module; a module's HIR claim starts when its own TLDR deps are ready, not when the parse phase ends |
| 2 | **Single-flight waiters have nothing to wait on.** `future()` returns `Future.pending()` and nothing completes it; waiters re-call `poll_artifact` (a polling loop); abandoned waiters leak `participants`. | #4372 | `src/compiler/80.driver/cache/daemon/cache_single_flight_v1.spl` (`me future`), `cache_daemon_main.spl` (`join_artifact`/`poll_artifact`) | single-flight = waiters get the leader's result; fully async | store a completer per flight; `complete()` resolves it; waiters await, never poll |
| 3 | **Daemon admission still takes an exclusive lock** (`cache_host_acquire_exclusive_lock_v1`, pre-existing, now the foundation of the single-flight host). | #4372 | `cache/daemon/cache_daemon_main.spl:32` | no locks | rename-published epoch file (exclusive create of `epoch.<n>`), no lock |
| 4 | **Over-limit is evict-then-write, and nothing enforces it.** `cache_eviction_plan_v1` evicts first; `cache_eviction_admit_write_v1` checks only after the plan; no publish path calls either (0 callers). | #4378 #4381 | `cache/gc/cache_eviction_plan_v1.spl:32,125,159`; `cache/metadata/cache_limits.spl:91-128` | over-limit **rejects** (design §12) | admit-before-plan on every publish; wire into the daemon publish path; see §3 corrected spec |
| 5 | **Third packed-blob container.** `packed_blob_view.spl` defines magic `SPLPKB01`, 32-B header, 24-B section entries, no digest/checksum, no 64-B alignment, no digest table — beside the `.spab` proposal (`SPLARTF1`) and `packed_binary_ast_v1.md` §7. It reads in place correctly (`sosix_file_map` + `rt_ptr_read_i64`, read-only, bounds-checked) but has **0 callers and no spec**. | #4397 | `src/lib/nogc_async_mut/sosix/packed_blob_view.spl:6-17,39-42,90,105-127` | packed §7/§8; one container | adopt the §7.1/§7.2 layout (64-B header, tagged checksums, digest table `0x0000`); wire into `frontend_parse_or_restore`; add the §5 specs |

### P1

| # | Finding | PR | path:line | Rule | Fix |
|---|---|---|---|---|---|
| 6 | Dead modules (0 callers outside own file/spec): lazy TLDR table; generic view table; `CacheReader`; `id_scope_file_v1`/`id_scope_local_v1`; `cache_eviction_*`; `cache_retention_limits_load_v1`; `reverse_reference_projection_v2`; `macro_expansion_cache_v1`; `macro_reference_projector`; `aspect_match_shard_v1` + `aspect_weave_*_v1`; `directory_join_point_facts_v1` | #4386 #4389 #4370 #4373 #4378 #4383 #4388 #4393 | `cache/reader/tldr_table_v1.spl`, `cache/generic_tldr_view_table_v1.spl`, `cache/reader/cache_reader_v1.spl:41`, `cache/id_scope_v1.spl:53,55`, `cache/gc/cache_eviction_plan_v1.spl:55,159`, `cache/reverse_reference_projection_v2.spl`, `cache/macro_expansion_cache_v1.spl`, `10.frontend/cache_artifact/macro_reference_projector.spl`, `00.common/cache_contract/aspect_match_shard_v1.spl`, `35.semantics/aspect_weave.spl` (new block) | design says "implemented" only with a live caller | each needs its one consumer PR or removal; no further module PRs without a caller |
| 7 | **Hash agility violated by every new digest.** Bare `sha256_text`/`sha256_u8_hex`/`xxh3_128_text` identities with no algorithm tag. | #4352 #4362 #4383 #4388 #4389 #4392 #4393 #4373 | `cache/module_artifacts_v1.spl:85,92,126-135`; `cache/reverse_reference_projection_v2.spl:135,146,149,267`; `cache/reverse_reference_receipt.spl:136,447`; `00.common/cache_contract/macro_reference_manifest_v1.spl:112,310,319`; `cache_artifact/macro_reference_projector.spl:180,298,299,333`; `cache/generic_tldr_view_v1.spl` (`source_digest`, `digest`, section digest); `00.common/cache_contract/aspect_match_shard_v1.spl:84`; `cache/id_scope_v1.spl:50` | packed §8 (≤3 algos, `(algo,len,bytes)`) | one `DigestV1 {algo_id, bytes}` type in `00.common/cache_contract/hash_algorithm_registry_v1.spl`; every site returns it; text form `sha256:<hex>` |
| 8 | **Fake async.** `cache_reader_read_v1` runs `get_blob` synchronously then wraps `Future.from_value`. | #4370 | `cache/reader/cache_reader_v1.spl` (`cache_reader_read_v1`) | fully async | return the gateway's own future |
| 9 | **Duplicate work instead of single-flight in the runner.** Each spec spawns `simple tldr` which re-parses imports the compile also parses. | #4352 | `src/app/test_runner_new/test_runner_single.spl:1185-1198` | single-flight; one parse | emit the companion from the compile's own parse via `SourceReader.update_tldr` (`cache/source_reader_v1.spl:56`) |
| 10 | **Producer re-parses and publishes text**, not the cached binary AST. | #4352 | `cache/module_artifacts_v1.spl:216,226` | rule 6 (entry = final AST) | project TLDR sections from the mapped blob (§7 `0x08xx` sections) |
| 11 | **Polling worker reaper.** `process_wait(pid, SHARD_POOL_POLL_MS)` round-robin with `continue`. | #4348 | `src/app/cli/native_build_main.spl:~935-945` | fully async, no spin | wait-any on the child set (`waitpid(-1)` / `WaitForMultipleObjects`) behind the portable layer (§4) |
| 12 | **Shard claim contention.** `file_create_exclusive` per module in one shared `queue_dir` (correct, no spin), plus every worker repeating the ~25 s closure walk and sharing one cache directory — the likely cause of the measured knee (8 workers 103 s; 16 → 114 s; 40 → 211 s). | #4380 #4368 | `src/compiler/80.driver/driver_source_pipeline_parsing.spl:230,237`; `native_build_main.spl` (`CAPSULE_PARSE_SHARD_DEFAULT_MAX = 8`) | NUMA/locality (§14) | precomputed per-worker module lists (no claim race); per-socket temp dirs; one closure walk published once (#4387 goes that way) |
| 13 | **Second eviction policy** beside `gc/admission.spl`, `gc/fast_gc.spl`, `gc/mark_sweep.spl`; **second reverse-reference index** beside `reference/reverse_reference_atomic_generation_v2.spl` + `reference/reverse_reference_coordinator_v1.spl`; **two shard-claim schemes** (exclusive-create markers for parse, ledger owner/queue for HIR/MIR) and **two spawn loops** (`spawn_parse_shards:703`, `run_ledger_shards:928`); **two TLDR section producers** (text `module_tldr_sections_v1` and AST `module_tldr_ast_sections_v1`). | #4378 #4383 #4348 #4368 #4380 #4354 #4355 | as named | one mechanism per concern | pick the owner; delete the other |
| 14 | `.rr` pointer temp name is pid-only (`"{pointer}.tmp.{rt_getpid()}"`): two writes from one process collide. | #4383 | `cache/reverse_reference_receipt.spl:252` | temp = pid + content | `{pid}.{xxh3(content)}` as #4364 does |
| 15 | Macro sections wired into the live `.tldr` producer **always with empty tables**; macro waiters get `"waiter"` and no result; each instance creates its own single-flight table. | #4388 #4392 | `cache/module_artifacts_v1.spl` (`_with_macros_v1` call), `cache/macro_expansion_cache_v1.spl` (`begin`) | dead output; single-flight | wire the projector or drop the call; return the flight future |
| 16 | **Seed heap registry is 64 `Mutex<HeapPtrSet>` shards** — still mutexes, still a global table (seed-only, Rust). | #4375 | `src/compiler_rust/runtime/src/value/heap.rs:222,231,307,346,598-609` | no mutexes (seed debt) | document as seed-only; per-thread arenas later |
| 17 | **No behavioural tests** for: lock-free claim (#4380), C transient raw table free/regrow (#4361: `src/runtime/runtime_memory.c:227,249`, lookup must return NULL at `cap==0`, `:122`), capsule wiring spec checks strings only (`bootstrap_capsule_shard_wiring_spec.spl`), #4364 live MIR/manifest write path, #4371 span change. Fixture-only specs: #4388 (4), #4393 (2). | as listed | — | tests must exercise the real owner | add owner-level specs before the next bootstrap run |

### P2

| # | Finding | PR | path:line | Fix |
|---|---|---|---|---|
| 18 | Struct/class spans now carry `file: path` → `ParserModule` span bytes change for every struct/class on the bootstrap fixed point; no spec. | #4371 | `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:~524-549` | fixed-point check + spec |
| 19 | Bare `xxh3_64` decides shard ownership, with a sign-bit workaround for an unfixed windows-gnu `>>` codegen bug. | #4368 | `src/compiler/80.driver/driver_parse_shard_hash.spl:15` | tag the hash; file the codegen bug |
| 20 | `aspect_weave_base_record_v1` copies the whole dict per insert (O(n²)); macro cache `_index` is a linear scan. | #4393 #4388 | `35.semantics/aspect_weave.spl`, `cache/macro_expansion_cache_v1.spl` | persistent map / Dict |
| 21 | Hard cap of 5 `--source` roots kept in sync by hand with `stage3_build_args_sha256`. | #4369 | `scripts/bootstrap/bootstrap-from-scratch.sh` | single owner for the roots list |
| 22 | `sosix/file_map.spl:19-21` says `file_mmap` was removed from `io/file_ops.spl`; it is still there. | pre-existing | `src/lib/nogc_sync_mut/io/file_ops.spl:414` | delete or fix the comment |
| 23 | No NUMA/affinity anywhere; workers only fan out. | all | — | §4 topology API |

### Per-PR status

| PR | Status | Tests | Live callers | Linux-ready |
|---|---|---|---|---|
| #4348 | P0 barrier, P1 polling reaper | wiring-string spec only | `bootstrap_main.spl:174` | spawn yes (`process_spawn_async` → cross-platform `rt_process_spawn_async`) |
| #4352 | P1 ×2 | real-owner spec | `simple tldr`, `source_reader_v1.spl:56`, runner | yes |
| #4354 / #4355 | ok; duplicate section producers | specs | via `module_artifacts_v1` | yes |
| #4360 | ok | spec | `tldr_entry.spl` | yes |
| #4361 | no spec | — | C runtime, `_Thread_local` globals | yes (portable C) |
| #4362 | P1 hash tags | spec | via producer | yes |
| #4364 | ok (temp = pid+content) | **no spec**, live path | MIR/manifest writes | yes (`rename(2)`) |
| #4365 | ok (linear-scan fallback) | Rust test | seed | yes |
| #4366 | docs + span spec | — | — | — |
| #4368 | P0 barrier (with #4348), P2 hash | 2 specs | `native_build_main.spl:1208` | yes |
| #4369 | P2 | none | script | yes |
| #4370 | P1 fake async; 0 callers | spec | none | yes |
| #4371 | P2 byte change, no spec | none | core bridge | yes |
| #4372 | **P0** no wakeup; P0 lock | spec | daemon host only | yes |
| #4373 / #4390 | P1 tag; file/local widths 0 callers | spec | global scope used by two dead tables | yes |
| #4375 | P1 mutex shards (seed) | Rust test | seed | yes |
| #4378 / #4381 | **P0** evict-then-write, 0 callers | plan-only spec | none | yes |
| #4379 | ok | spec | `driver_hir_cache.spl` | yes |
| #4380 | ok claim (no spin); P1 contention; no spec | none | `driver_source_pipeline_parsing.spl:237` | `file_create_exclusive` → `O_EXCL` on POSIX (`runtime_native.c:15027`) |
| #4383 | P1 tags, pid-only temp, duplicate index, 0 callers | specs | none | yes |
| #4386 | 0 callers | spec | none | yes |
| #4387 | ok; publication path unverified for temp+rename | none | 2-3 files | likely |
| #4388 / #4392 | P1 ×4, 0 callers for cache/projector | fixture-only ×4 | manifest types only | yes |
| #4389 | P1 tags; view table 0 callers | specs | projector live | yes |
| #4393 | P1 tags, 0 callers, P2 O(n²) | fixture-only ×2 | none | yes |
| #4397 | **P0** third container, 0 callers, no spec | none | none | `sosix_file_map` has mmap + MapViewOfFile |

## 2. What the design-status rows become

`src_based_tldr_build_v1.md` rows marked "implemented, uncalled" stay so; add
"**non-conforming**" to: single-flight (#4372, no wakeup + lock), cache limits
(#4378, evict-then-write), packed view (#4397, container), CacheReader
(#4370, fake async). The per-file-jobs row stays **partial** with finding 1 as
the blocker.

## 3. Cache limits — corrected spec (user item 12)

What #4378/#4381 cover: global `memory_max_bytes`, `storage_max_bytes`,
`max_branches`, `kept_branches`, `versions_per_source`
(`cache/metadata/cache_limits.spl:91-128`; env `SIMPLE_CACHE_MEMORY_MAX_BYTES`,
`SIMPLE_CACHE_MAX_BYTES`, `SIMPLE_CACHE_MAX_BRANCHES`,
`SIMPLE_CACHE_KEPT_BRANCHES`; host keys `cache_max_bytes`, `c…` in
`scripts/setup/host-env.shs` / `src/lib/common/config_core/host_config.spl`).
Eviction order (`cache_eviction_plan_v1.spl:3-16`): per (branch, source) keep
`versions_per_source` newest → drop branches beyond `max_branches` (kept first)
→ LRU to `storage_max_bytes` → unload LRU to `memory_max_bytes`.

**Gaps:** (a) no **per-source SIZE** cap — only a version count; (b) no
**per-branch** memory or storage budget — only global; (c) over-limit is
evict-then-admit, the rule is **reject**; (d) no enforcement point (daemon has
no request loop or usage ledger; `cache_eviction_admit_write_v1` has 0
callers); (e) no accounting of what an entry *is* (AST blob, TLDR, object,
lib/dynlib/binary) — `CacheEntryUseV1` has only bytes; (f) `kept_branches`
list is untagged text; (g) memory accounting source undefined (mapped bytes vs
resident).

### 3.1 Config keys (env → host.sdn → default; all counts/bytes are i64)

| Key (env / host.sdn) | Scope | Default | Meaning |
|---|---|---|---|
| `SIMPLE_CACHE_MEMORY_MAX_BYTES` / `cache_memory_max_bytes` | global | 1 GiB | sum of **mapped** bytes of live views (not RSS) |
| `SIMPLE_CACHE_MAX_BYTES` / `cache_max_bytes` | global | 10 GiB | on-disk bytes under the one root |
| `SIMPLE_CACHE_MAX_BRANCHES` / `cache_max_branches` | global | 4 | distinct branch namespaces retained |
| `SIMPLE_CACHE_KEPT_BRANCHES` / `cache_kept_branches` | global | `main` + `release/*` | never evicted by count |
| `SIMPLE_CACHE_BRANCH_MEMORY_MAX_BYTES` / `cache_branch_memory_max_bytes` | per branch | global/`max_branches` | **new** |
| `SIMPLE_CACHE_BRANCH_MAX_BYTES` / `cache_branch_max_bytes` | per branch | global/`max_branches` | **new** |
| `SIMPLE_CACHE_VERSIONS_PER_SOURCE` / `cache_versions_per_source` | per (branch, source) | 3 | entries kept per source **per artifact kind** |
| `SIMPLE_CACHE_SOURCE_MAX_BYTES` / `cache_source_max_bytes` | per (branch, source) | 64 MiB | **new**: bytes across all versions and kinds of one source, on disk **and** mapped |
| `SIMPLE_CACHE_ARTIFACT_KINDS` / `cache_artifact_kinds` | — | `ast,tldr,obj,lib,dynlib,bin` | kinds counted; `lib/dynlib/bin` count against the **entry source = link action key**, not against any source file |

### 3.2 Accounting source (lock-free)

- One append-only **usage ledger** per branch: `ledger/<branch>/<epoch>.sdn`
  rows `(entry_id, kind, source_key, version_key, disk_bytes, mapped_bytes,
  last_used_ms)`, written by the producer at publish (temp+rename of the
  ledger segment, one segment per producer process → no shared writer), read
  by the daemon's single loop which folds segments into an in-memory
  `CacheUsageV1` (plain values; no lock). `last_used` is bumped by readers
  appending a touch row to their own segment.
- `disk_bytes` = file length; `mapped_bytes` = mapping length while a view is
  live (reader appends open/close rows); a crashed reader's segment expires
  with its epoch (no lease: the epoch is the producer identity + pid, and a
  dead pid's rows are dropped on the next fold).
- Every `source_key`, `version_key` and ledger digest is `DigestV1`
  (algo-tagged, packed §8); `kept_branches` entries are branch names, matched
  as text.

### 3.3 Eviction algorithm (daemon fold; pure function of ledger → plan)

1. **Admit first.** For an incoming publish of `n` bytes: if any of (source
   size, branch bytes, global bytes) would exceed its cap **after** the plan
   below, **reject** (return `rejected: <limit>`; producer keeps its result in
   memory for this job and does not publish). Never evict to make room for
   this write.
2. Per (branch, source, kind): keep the `versions_per_source` most recently
   used; evict the rest.
3. Per (branch, source): while bytes > `cache_source_max_bytes`, evict LRU
   versions (any kind) down to the cap.
4. Per branch: while bytes > `cache_branch_max_bytes`, evict LRU entries.
5. Branches: beyond `max_branches`, drop whole branches not in
   `kept_branches`, least-recently-used first.
6. Global: while disk > `cache_max_bytes`, evict LRU across branches.
7. Memory: steps 3–6 again on `mapped_bytes` with the memory caps; the action
   is **unmap** (readers re-map on next use), never a disk delete.
8. Eviction = temp-free: rename the entry to `trash/<epoch>/` (atomic), delete
   in a later fold once no live-view row references it.

### 3.4 Gaps for the implementer

| Gap | Where |
|---|---|
| per-source size cap, per-branch budgets, kind column | `cache_limits.spl` `CacheRetentionLimitsV1`, `cache_eviction_plan_v1.spl` `CacheEntryUseV1` |
| admit-before-plan + reject | `cache_eviction_admit_write_v1` semantics inverted; call from the publish path |
| the publish path itself | daemon has no request loop; the one producer today is `module_artifacts_emit_v1` + `frontend_shared_parse_store_v1` — both must consult admission |
| ledger segments | new `cache/metadata/cache_usage_ledger_v1.spl`; no file lock |
| mapped-bytes accounting | hook in `sosix_file_map`/`unmap` wrapper used by the view |
| tagged digests | `DigestV1` everywhere in limits/ledger |
| merge with `gc/admission.spl`, `fast_gc.spl` | one eviction owner |

## 4. Linux / macOS / FreeBSD behaviour and the platform-neutral layer

### 4.1 Per mechanism

| Mechanism | Windows today | Linux / macOS / FreeBSD | Change needed |
|---|---|---|---|
| **mmap** | `CreateFileMapping`+`MapViewOfFile` via `rt_mmap` (`sosix/file_map.spl:5-9`; Rust seed `file_ops.rs:1530/1594`, C `runtime_native.c` `rt_file_map_*`) | `mmap(2)` `PROT_READ, MAP_PRIVATE`; `madvise(WILLNEED)` prefetch; page size 4 KiB (16 KiB on Apple silicon, so 64-B section alignment is fine but **mapping offsets must be page-aligned on all three**); munmap vs `UnmapViewOfFile` | none for the view if it uses `sosix_file_map`; forbid raw `rt_mmap` imports (file_map.spl rule); add `page_size()` to the layer (exists in `DedicatedHost`) |
| **atomic rename** | `MoveFileExW(REPLACE_EXISTING|WRITE_THROUGH)` with long-path prefix (`runtime_native.c:15068,16127-16134`); fails with sharing violation if the destination is **open without `FILE_SHARE_DELETE`**, and a loaded DLL/EXE can never be replaced | `rename(2)` is atomic and replaces an open or executing file (inode swap); FreeBSD/macOS same; Darwin `renamex_np` not needed | layer `publish_atomic(temp, dst)`; on Windows open cache files with `FILE_SHARE_DELETE` (readers) so producers can replace; dynlib/bin outputs must be published to a **new versioned name** and switched via a small manifest rename, never replaced in place (Windows lock) |
| **exclusive create** | `_open(_O_CREAT|_O_EXCL|_O_BINARY)` (`runtime_native.c:15022`); `CREATE_NEW` in the async path (`platform/async_windows.c:534`) | `open(O_CREAT|O_EXCL, 0600)` (`:15027`) — atomic on local FS; **not** reliable on NFS v2 / some SMB; fine on local ext4/xfs/apfs/ufs | layer `create_exclusive(path, bytes)`; document "cache root must be a local filesystem" |
| **dynlib** | `.dll` + `.dll.a` import lib (mingw) / `.lib` (msvc); `LoadLibraryW` (`runtime_native.c:9720`); search = exe dir + PATH | `.so` / `.dylib`; `dlopen(RTLD_NOW|RTLD_LOCAL)` (`:2534`); search = `rpath`/`RUNPATH` (`-Wl,-rpath,$ORIGIN/..`), `DT_NEEDED` sonames, `LD_LIBRARY_PATH`; macOS `@rpath`/`@loader_path`, `install_name`; FreeBSD like Linux (`$ORIGIN` needs `-z origin`) | layer `dynlib_file_name(stem)`, `import_lib_name(stem)`, `rpath_args(target)`; cache keys for objects/libs already fold the target triple (`native_build_environment_identity.spl`) — keep |
| **process spawn** (shard workers) | `process_spawn_async` → `rt_process_spawn_async` (CreateProcess); self re-exec via `self_exe()`; argv passed as a list (no shell quoting) | fork/exec or `posix_spawn`; `self_exe()` = `/proc/self/exe` (Linux), `_NSGetExecutablePath` (macOS), `sysctl KERN_PROC_PATHNAME` (FreeBSD); no `.exe`; `native_build_main.spl:87` already accepts `/simple` | layer `spawn(argv) -> child`, `wait_any(children)`, `self_exe()`; replace the `process_wait(pid, poll)` loop (P1 #11) with `wait_any` |
| **NUMA / topology** | processor groups (>64 LPs need `SetThreadGroupAffinity`); `GetLogicalProcessorInformationEx` | `sched_setaffinity`, `/sys/devices/system/node/node*/cpulist`, optional libnuma; macOS has **no** affinity API (hint only via `thread_policy_set`), FreeBSD `cpuset_setaffinity` | layer `cpu_topology() -> {sockets, cpus_per_socket, cpu_count}` + `pin_current_thread(cpuset)` (no-op where unsupported); today only `rt_cpu_count` (`sffi/system.spl:231`) |
| **paths / case / symlinks** | case-insensitive, `\` and `/`, long-path prefix `\\?\`, drive letters, junctions | case-sensitive (Linux/FreeBSD), case-insensitive-preserving default on macOS; symlinks everywhere | logical module key = `frontend_shared_parse_logical_path_v1` (already case-normalised, `/`-separated); never use the host path in a key; `rt_file_is_regular_no_follow` exists — use it on every cache open |
| **text vs binary I/O** | `_set_fmode(_O_BINARY)` globally (`runtime_native.c:3313-3323`); `file_write_bytes` (`io_runtime.spl:342`) | no distinction | none; forbid `file_write` (text) for blobs — blob writers use `file_write_bytes` only |
| **line endings** | CRLF checkouts possible (`.gitattributes`) | LF | source content key must hash the **bytes as read**; the cache key already does; `.tldr` text companions must be written with `\n` only (they are) |
| **page size / alignment** | 4 KiB; allocation granularity 64 KiB for `MapViewOfFile` offsets | 4 KiB (16 KiB Apple silicon, also some aarch64 Linux kernels with 64 KiB) | map whole files from offset 0 (the design does); section alignment 64 B is independent of page size |

### 4.2 One platform-neutral layer

Simple-first, with the existing thin C/rt twins behind it (repo rule:
`doc/07_guide/os/hal/pure_simple_hal.md`). Proposed single owner:
`src/lib/nogc_sync_mut/platform/host_io.spl` (sync surface) +
`src/lib/nogc_async_mut/platform/host_io_async.spl` (futures over the same
externs). Compiler, cache and runner code import **only** these; a `git grep`
guard (`scripts/check/check-no-os-branches-in-compiler.shs`) fails on
`is_windows`/`"windows"`/`\\`/`.exe`/`.dll` inside `src/compiler/80.driver/cache`,
`src/compiler/10.frontend` (except `cfg_platform.spl`, which is *target*
configuration, not host), `src/app/cli/native_build_main.spl`.

| Surface | Reuse (exists) | Missing |
|---|---|---|
| `file_read_bytes / file_write_bytes / file_size / file_exists / is_regular_no_follow` | `std.nogc_sync_mut.io_runtime` (`:319-342`), `rt_file_is_regular_no_follow` | async twins in `nogc_async_mut/async/io.spl` |
| `map_readonly(path) -> MappedView`, `unmap`, `prefetch`, `page_size` | `nogc_async_mut/sosix/file_map.spl` (`sosix_file_map/unmap/prefetch`), `common/platform/dedicated_host.spl` (`DedicatedHost.page_size`, `mmap/munmap/mprotect`) | one typed `MappedView {addr, len}` instead of raw `i64`; retire `io/file_ops.spl:414 file_mmap` and raw `rt_mmap` imports |
| `publish_atomic(temp, dst)` | `rt_file_rename` (`runtime_native.c:16127-16136`), pattern in `module_artifacts_v1.spl:150`, `incremental.spl:600` | one helper `publish_atomic_bytes(dst, bytes)` = temp(pid+content) + rename, used by all four writers; Windows readers open with share-delete |
| `create_exclusive(path, bytes)` | `rt_file_create_excl` (`io/file_bytes.spl:23,41`), `file_create_exclusive` (`io/file_ops.spl:253`) | one name; document local-FS requirement |
| `spawn(argv)`, `wait_any`, `self_exe` | `io/process_ops.spl:815-860` (`rt_process_spawn_async_value`, `_piped`, `_pinned_piped`), `self_exe()` in `native_build_main.spl` | `wait_any` (today per-pid polling); move `self_exe` into the layer |
| `dynlib_name / import_lib_name / rpath_args / dlopen` | `sffi/dynamic.spl:29,155` (`spl_dlopen`), `sffi/guest_dlopen.spl` | naming + rpath helpers (today scattered in linker code) |
| `cpu_topology / pin_thread` | `sffi/system.spl:231` (`rt_cpu_count`) | sockets/NUMA nodes, affinity (no-op on macOS) |
| `logical_path(path)` | `frontend_shared_parse_logical_path_v1` | move to the layer; make it the only key input |

Verification: `sh scripts/check/check-dual-run-shadow.shs` (C/Simple twin gate)
for each new extern; a selftest fixture per surface on Linux and Windows CI
(`required-gates.yml` extended job).

## 5. Recommended order

1. Fix the two live P0s: wake-up future in `cache_single_flight_v1` (+ remove
   the admission lock); per-module job pool replacing the parse/HIR/MIR phases.
2. Converge on one packed container (§7 of the packed doc) by rewriting
   `packed_blob_view.spl`'s header/table; wire it into
   `frontend_parse_or_restore`; land the §5 specs.
3. `DigestV1` + registry; sweep the P1 hash sites.
4. Cache limits per §3; one eviction owner; admission on the publish path.
5. Platform layer (§4.2) + the no-OS-branch guard; replace the polling reaper
   with `wait_any`.
6. One consumer PR per dead module, or delete it.
