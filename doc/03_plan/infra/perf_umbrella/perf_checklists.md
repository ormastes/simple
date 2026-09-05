# Performance Optimization — Per-Domain Checklists (AC-2)

Generated: 2026-06-13. Derived from `doc/07_guide/compiler/check_perf.md`, existing harnesses,
and research notes in `.spipe/perf-opt-lang-web-db-os/research/`.

Each section has:
- Domain-specific pass/fail items tied to a concrete harness, metric, or spec file.
- An **API/arch-guard row** (AC-8): `scripts/check/check-api-arch-guard.shs` must stay green.
- An **rt_* reduction row** (AC-9): measured vs baseline (nogc_sync_mut 7,974 lines; nogc_async_mut 2,249 lines).

Status key: **CLOSED** = already done/verified; **PARTIAL** = infrastructure exists but gaps remain; **OPEN** = not yet started.

---

## 1. Language — Script (Interpreter)

Harness: `sh scripts/check/check-cross-language-perf.shs` in interpreter mode (`simple file.spl`).
Spec: `test/01_unit/app/interpreter/perf_spec.spl`, `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` (to be created).

### Baseline & Measurement
- [x] **[OPEN]** Capture P0 baseline: interpreter (`script`-mode) rows captured; report `doc/09_report/perf/perf_baseline_2026-06-13.md`, persistent table `doc/10_metrics/perf/perf_baseline_table.md`. — verified doc/10_metrics/perf/perf_baseline_table.md:5 `| name | mode | metric | value | unit | arch |`
  - divergence: planned `interp_baseline_<date>.md` / `interp_baseline.md`; shipped `perf_baseline_2026-06-13.md` / `perf_baseline_table.md` (interpreter rows carry `mode=script`, not a separate file).
- [x] **[OPEN]** `lang_script_vs_compiler_bench_spec.spl` (AC-4) exists and emits benchmark docs; interpreter row is separate from compiler rows. — verified test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl:130 `bench_emit`

### Startup
- [ ] **[CLOSED]** Cold startup ≤ reference (interpreter instant-start advantage vs bun/python confirmed); re-verify after any loader change via `check-startup-size-performance-audit.shs` (report generator only — its only fail arms are `mmap-preload-gate`/`network-libs-gate`/`network-size-gate` at :721/:742/:759; it asserts NO startup-timing verdict, so this box needs a real comparison gate).
- [ ] **[OPEN]** Cold startup re-measured post-P1 opts and recorded in `doc/10_metrics/perf/interp_baseline.md`.

### Warm Throughput
- [ ] **[CLOSED]** `debug_state` atomics contention eliminated (micro-opt DONE per research).
- [ ] **[CLOSED]** `extern dispatch` map lookup optimized (micro-opt DONE per research).
- [x] **[CLOSED]** Allocator: mimalloc wired for interpreter heap (DONE per research). — verified src/compiler_rust/driver/src/main.rs:70 `#[global_allocator] static GLOBAL: TrackingAlloc<mimalloc::MiMalloc>`
- [ ] **[CLOSED]** Linker: mold used for seed builds (DONE per research).
- [x] **[CLOSED]** Parallel compilation/link: rayon thread-pool integration landed. — verified src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:192 `rayon::ThreadPoolBuilder::new()`
  - divergence: planned parallel *eval* (interpreter); shipped rayon in the native-project compile pipeline and `linker/parallel.rs` — no rayon use found on the interpreter eval path.
- [ ] **[OPEN]** MIR bulk-ops recognizer phases 2–8 landed in `src/compiler/60.mir_opt/optimization_passes.spl` **and** re-measured in interpreter mode (RISK: false bulk-copy recognizer regresses all 3 modes — gate behind regression spec before landing).
- [ ] **[OPEN]** String-copy minimization in `src/lib/nogc_sync_mut/` stdlib collections landed and warm-throughput delta recorded.

### Per-Op Cost
- [ ] **[OPEN]** `test/01_unit/app/interpreter/perf_spec.spl` green at per-op budget thresholds (fib35 in-process, method dispatch in `test/05_perf/bench/method_dispatch_bench.spl`, bytes_push 1 MiB in `test/05_perf/bytes_push_1mib.spl`).
- [ ] **[OPEN]** Tiered JIT hotspot spec `test/01_unit/compiler/interpreter/tiered_jit_hotspot_spec.spl` green.

### API/Arch Guard (AC-8)
- [ ] **[OPEN]** `scripts/check/check-api-arch-guard.shs` green after every interpreter-layer change; public symbol diff (`src/compiler/90.tools/symbol_analyzer.spl` + `src/compiler/99.loader/metadata_symbol_surface.spl`) shows zero unintended removals; snapshot stored in `doc/08_tracking/api_surface/`.

### rt_* Reduction (AC-9)
- [x] **[OPEN]** Baseline rt_* count captured in `doc/10_metrics/perf/rt_baseline_2026-06-13.md`: app-developer view `examples/**.spl` raw call sites = 3,225; `src/lib/nogc_async_mut/**` `extern fn rt_*` decls = 118. — verified doc/10_metrics/perf/rt_baseline_2026-06-13.md:9 `Raw counts`
  - divergence: planned a `nogc_sync_mut` line count of 7,974 in `rt_baseline.md`; shipped a dated `rt_baseline_2026-06-13.md` measuring the app-developer (`examples/`) view plus `nogc_async_mut` extern decls instead.
- [ ] **[OPEN]** After sweep: count re-measured; reduction vs baseline recorded; no direct `rt_*` calls visible in example/app-developer code paths.

---

## 2. Language — Compiler (SMF + Native)

Harness: `bin/simple run src/app/test/bench/bench_baseline_driver.spl` emits
script and SMF-mode language baseline rows by compiling
`src/app/test/bench/bench_smf_workload.spl` to SMF and parsing its self-timed
output. Keep `sh scripts/check/check-cross-language-perf.shs` for the separate
C/Go/pherallel comparison harness.
Specs: `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` (AC-4); `test/02_integration/app/simple/smf_cache_reuse_spec.spl` (AC-7).

### Baseline & Measurement
- [ ] **[OPEN]** Capture P0 baseline: SMF and native rows separate from interpreter row; save to `doc/09_report/perf/compiler_baseline_<date>.md`.
- [ ] **[OPEN]** `lang_script_vs_compiler_bench_spec.spl` emits benchmark docs with arch tag `x86_64` and mode tags `smf`/`native`; doc emitted to `doc/09_report/`.

### Compile Time
- [ ] **[OPEN]** Compile-time regression gate: re-run `compiler_perf_baseline_spec.spl` (`test/05_perf/compiler_perf_baseline_spec.spl`) after every MIR-opt phase; no >5% regression vs P0 baseline.
- [ ] **[OPEN]** MIR bulk-ops phases 2–8 (`optimization_passes.spl`) landed; compile-time delta measured and within budget.

### Artifact Size
- [ ] **[OPEN]** Binary size audited via `check-startup-size-performance-audit.shs` after each native build change; size table updated in `doc/10_metrics/perf/compiler_baseline.md`.

### Warm Throughput
- [ ] **[OPEN]** SMF warm throughput (`bench_baseline_driver.spl` SMF-mode rows
  from `bench_smf_workload.spl`) re-measured post-P1 and recorded.
- [ ] **[OPEN]** Native Cranelift AOT throughput (`check-cross-language-perf.shs` native mode) re-measured; `pure_simple_ctype_perf_gap` (Cranelift no inlining) either resolved or filed as explicit open bug with measurement.
- [x] **[CLOSED]** Parallel workers (rayon/green-thread) benchmarked via `check-cross-language-perf.shs` `WORKERS`/`FANOUT_WORKERS` dimensions (DONE per research). — verified scripts/check/check-cross-language-perf.shs:1801 `pool_evidence "$SIMPLE_BINARY .../parallel_multicore_green_simple.smf" "$MULTICORE_GREEN_WORKERS"`

### Cache Reuse (AC-7)
- [x] **[PARTIAL — BUILD]** `src/app/startup/dynsmf_autoload.spl`: queued background-compile command actually dispatches via `process_spawn_async` and records a `dispatched` evidence row carrying the pid. — verified src/app/startup/dynsmf_autoload.spl:56 `process_spawn_async`
- [x] **[PARTIAL — BUILD]** `src/os/smf/dynsmf_session.spl`: content-hash guard added to the dynSMF precompiled lane — a `<artifact>.srchash` sidecar is compared against the current source hash after the magic-bytes check. — verified src/os/smf/dynsmf_session.spl:188 `val sidecar = dynsmf_srchash_path(artifact_path)`
  - divergence: planned SHA-256 at `dynsmf_session.spl:163`; shipped an `rt_hash_text`-based srchash/ifacehash sidecar pair in `src/os/smf/dynsmf_session.spl` (not SHA-256, and the file moved out of the planned path).
- [x] **[MISSING — BUILD]** `test/02_integration/app/simple/smf_cache_reuse_spec.spl` created: exercises the srchash-sidecar cache hit (unchanged source) and stale-source miss, plus absent-sidecar and invalid-magic rejection. — verified test/02_integration/app/simple/smf_cache_reuse_spec.spl:62 `accepts artifact when sidecar hash matches current source hash (cache hit)`
  - divergence: planned to drive `try_load_smf_cached`; shipped drives `dynsmf_artifact_status_with_hash_injected` over the dynSMF srchash lane. "Green" is not asserted here — no run was performed.
- [x] **[EXISTS]** Unchanged-script SMF cache reuse (`simple run`): `try_load_smf_cached` + SMF manifest + `validate_smf` pipeline present. — verified src/compiler/80.driver/driver_api_interpret.spl:28 `try_load_smf_cached`
- [x] **[EXISTS]** Stale-source cache miss (user scripts): source-hash + options-hash + dependency interface hashes compared in `cache_validator.spl`; a mismatch returns `cache_check_result_stale`. — verified src/compiler/80.driver/cache/cache_validator.spl:172 `if current_src_hash != smf_source_hash: return cache_check_result_stale(...)`
  - divergence: planned SHA-256; shipped `hash_text` (:171) as the source-hash primitive.
- [x] **[EXISTS]** Idle background compile via watcher daemon: `WatcherDaemon.generate_smf()` on file-change. — verified src/compiler/80.driver/watcher/watcher_daemon.spl:138 `self.generate_smf(self.request_for_changed_file(path))`

### API/Arch Guard (AC-8)
- [ ] **[OPEN]** `scripts/check/check-api-arch-guard.shs` green after every compiler/SMF change; public symbol snapshot diffed; snapshot in `doc/08_tracking/api_surface/`.

### rt_* Reduction (AC-9)
- [ ] **[OPEN]** rt_* sweep in `nogc_sync_mut` stdlib completed; compiler-generated code paths do not surface raw `rt_*` to app-developer imports.

---

## 3. Web Server

Harness: `test/05_perf/web/web_server_bench_spec.spl` (to be created, AC-3).
Related existing specs: `test/05_perf/http_server/` (existing), `test/05_perf/bench/`.
Note: pre-existing failures in `rate_limit_spec`, `request_validation_spec`, `security_headers_spec` (refactor `cd46a9463a4`) must be quarantined/fixed before AC-8 baseline is captured — they must not count as AC-8 regressions.

### Baseline & Measurement
- [x] **[OPEN]** `web_server_bench_spec.spl` created with arch tag `x86_64`; emits benchmark docs to `doc/09_report/perf/web_server_bench.md` and persistent table to `doc/10_metrics/perf/web_server_bench.md`. — verified test/05_perf/web/web_server_bench_spec.spl:200 `it "bench_emit writes report and metrics files"` (paths at :71-72)
  - divergence: planned dated `web_baseline_<date>.md` + `web_baseline.md`; shipped fixed-name `web_server_bench.md` in both trees (the report file self-dates in its header instead).
- [ ] **[OPEN]** P0 baseline captured: cold-start ms, req/s, p50 latency ms, p99 latency ms, peak RSS MB all recorded as separate columns.

### Cold Start
- [ ] **[CLOSED]** H2 server (`HttpServer` with ALPN), H3/QUIC, and unified entry all implemented (`web-server-optimizer-complete` CLOSED 2026-05-25) — cold-start overhead locked in. (`src/lib/nogc_sync_mut/http/h2/` and `.../h3/` trees and `src/lib/nogc_async_mut/http_server/server.spl:165 class HttpServer` exist, but the tree's only `ALPN` occurrence is a comment at `h2/h2_preface.spl:3` — no ALPN negotiation code found, so the compound claim is unproven.)
- [ ] **[OPEN]** Cold-start measurement via `web_server_bench_spec.spl` run and recorded.

### Request Throughput (req/s)
- [ ] **[OPEN]** Throughput measured under `web_server_bench_spec.spl` at concurrency 1, 10, 100; results in benchmark doc.
- [ ] **[CLOSED]** Static file serving: sendfile/zero-copy, pre-compressed cache, mmap, ETag, Range all implemented (`web-server-optimizer-complete`).
- [ ] **[CLOSED]** Network acceleration: TCP state machine, `NetBackendCapabilities` tiers, DMA RX/TX buffers implemented (`net-acceleration-remaining` CLOSED 2026-05-20).

### p50 / p99 Latency
- [ ] **[OPEN]** p50 and p99 latency measured by `web_server_bench_spec.spl`; p99 target recorded in plan (set during P0 baseline run).

### Peak RSS
- [ ] **[OPEN]** Peak RSS under load measured by `web_server_bench_spec.spl`; recorded in benchmark doc.
- [ ] **[OPEN]** Bounded-read end-to-end spec (injectable stream seam for `parse_request`) created — recorded as concrete follow-up in `webserver_harden` log.

### API/Arch Guard (AC-8)
- [ ] **[OPEN]** Three broken pre-existing specs (`rate_limit_spec`, `request_validation_spec`, `security_headers_spec`) either fixed or explicitly excluded with justification documented in `doc/08_tracking/api_surface/web_quarantine.md` before guard baseline is captured.
- [ ] **[OPEN]** `scripts/check/check-api-arch-guard.shs` green for web server public API (`HttpServer`, `HttpRequest`, `HttpResponse`, `parse_request_with_limits`, `path_is_safe`); snapshot in `doc/08_tracking/api_surface/`.

### rt_* Reduction (AC-9)
- [ ] **[OPEN]** rt_* count in web server request path (`src/lib/nogc_sync_mut/src/net/`, `src/lib/nogc_async_mut/`) measured vs baseline; reduction recorded.

---

## 4. Database — RAM-Only

Harness: `test/05_perf/db/db_ram_vs_persistent_bench_spec.spl` (to be created, AC-5).
Target code: `database/pure_sql/database.spl` (`PureDatabase` opened without file path) and `db/db_persistence.spl` (`DbTable`, heap-only).
Note: SQLite FFI wrapper (`database/sql/`) unavailable in interpreter mode — benchmarks must specify mode.

### Baseline & Measurement
- [x] **[OPEN]** `db_ram_vs_persistent_bench_spec.spl` created; RAM-only section uses `PureDatabase` in-memory and emits via `bench_emit`. — verified test/05_perf/db/db_ram_vs_persistent_bench_spec.spl:275 `it "ram-only: insert N rows and count == N (correctness oracle)"` (label at :49, emit at :344)
  - divergence: planned label `ram-only` and a dated `db_baseline_<date>.md`; shipped mode label `ram` emitted through the shared `bench_emit` report/table pair.
- [ ] **[OPEN]** P0 baseline captured: insert throughput (rows/s), point-query throughput (queries/s), range-scan throughput; all recorded separately from persistent rows.

### Insert Throughput
- [ ] **[OPEN]** Insert throughput (rows/s) for 1k, 10k, 100k rows measured in `db_ram_vs_persistent_bench_spec.spl` RAM section; MVCC snapshot scan O(N) over dead tuples noted as known constraint.

### Query Throughput
- [ ] **[OPEN]** Point-query and FTS (`PrefixIndex`, `TextIndex` in-memory) throughput measured; index-aware query path in `db_query.spl` exercised (note: phases 6/7/8 of `db-hardening-optimizer-general` still open — mark results accordingly).

### API/Arch Guard (AC-8)
- [ ] **[OPEN]** `scripts/check/check-api-arch-guard.shs` green for `PureDatabase` public API; snapshot in `doc/08_tracking/api_surface/`.

### rt_* Reduction (AC-9)
- [ ] **[OPEN]** rt_* count in `database/pure_sql/` measured; reduction target recorded after sweep.

---

## 5. Database — Persistent

Harness: `test/05_perf/db/db_ram_vs_persistent_bench_spec.spl` (same file, separate section, AC-5).
Target code: `PureDatabase._persist()` → `_serialize_disk()` path (text `_persist`); `db/dbfs_engine/mvcc.spl` (WAL/DBFS-backed). Results must be separate from db-RAM rows.

### Baseline & Measurement
- [x] **[OPEN]** Persistent section of `db_ram_vs_persistent_bench_spec.spl` uses `PureDatabase.open_deferred(path)` + `checkpoint()`; WAL section uses `MvccTable`; results emitted with labels `persistent` and `wal` separately. — verified test/05_perf/db/db_ram_vs_persistent_bench_spec.spl:51 `val WAL_MODE: text = "wal"` and :157 `fn run_wal_insert_count`
  - divergence: planned the persistent lane to be plain file-path `PureDatabase` and the WAL lane to call `db/dbfs_engine/mvcc.spl` directly; shipped `open_deferred`+`checkpoint` and the in-process `MvccTable` façade.
- [ ] **[OPEN]** P0 baseline captured: insert throughput, query throughput, persist cost (ms/mutation) recorded. Reference point: deferred INSERT 200 rows = 954ms (`pure-db-perf-improve` CLOSED 2026-05-27, `doc/09_report/pure_db_perf_comparison_2026-05-26.md`).

### Insert + Persist Cost
- [ ] **[OPEN]** Per-mutation `_persist()` cost measured (expected O(N) file-write); `open_deferred` + `checkpoint` flow measured as deferred batch alternative; results recorded.
- [ ] **[OPEN]** WAL path (`mvcc.spl`) insert throughput measured; WAL replay blank-row P0 bug (`simple-db-hardening` finding) resolved or explicitly blocked with bug reference before benchmark is treated as authoritative.
- [ ] **[OPEN]** Incremental FTS rebuild (`_ensure_fts_index`, lazy rebuild): cost measured; 0ms rebuild after optimization confirmed or re-measured.

### Query Throughput
- [ ] **[OPEN]** Point-query throughput on persistent store (file-backed, `_deserialize_row` O(N) per query) measured and compared to RAM-only row.
- [ ] **[OPEN]** WAL-backed query throughput measured separately.

### rt_file_create_excl Gap (AC-9 / correctness pre-condition)
- [x] **[OPEN]** `rt_file_create_excl` extern landed (TOCTOU lock fix F2) in both the C runtime and the pure-Simple core. — verified src/runtime/runtime_legacy_core.c:515 `int rt_file_create_excl(...)` and src/runtime/simple_core/core_fs.spl:445 `pub fn rt_file_create_excl`

### API/Arch Guard (AC-8)
- [ ] **[OPEN]** `scripts/check/check-api-arch-guard.shs` green for persistent DB public API (`PureDatabase._persist`, `open_deferred`, `checkpoint`, `dbfs_engine` surface); snapshot in `doc/08_tracking/api_surface/`.

### rt_* Reduction (AC-9)
- [ ] **[OPEN]** rt_* count in `db/dbfs_engine/` and `database/pure_sql/` persistence paths measured; reduction target recorded after sweep.

---

## 6. OS (x86_64)

Harness: `test/05_perf/os/os_fs_sched_bench_spec.spl` (to be created, AC-3) + QEMU systest (`test/03_system/os/qemu/`).
Model: `test/03_system/os/qemu/os/` layout (`common/qemu_os_config.spl`, `common/qemu_os_harness.spl`, per-arch spec files).
Related closed work: `fs-hardening-optimization` CLOSED 2026-05-23, `fs-opt-general` CLOSED 2026-05-23, `scheduler-process-isolation` CLOSED 2026-05-20.

### Baseline & Measurement
- [x] **[OPEN]** `os_fs_sched_bench_spec.spl` created with arch tag `x86_64`; emits benchmark docs via `bench_emit`; a QEMU systest variant is stubbed `pending()` for the systest lane. — verified test/05_perf/os/os_fs_sched_bench_spec.spl:54 `val ARCH_TAG: text = "x86_64"` and :230 `pending("qemu boot bound — runs in systest lane")`
  - divergence: planned to use the `qemu_os_harness.spl` model and emit a dated `os_baseline_<date>.md`; shipped a HOST-PROXY spec (`mode=host_x86_64`, real fs/spawn on the host) with the QEMU variant left pending — so no in-guest number is produced by this spec.
- [ ] **[OPEN]** P0 baseline captured: fs read throughput (MB/s), fs write throughput (MB/s), exec/spawn latency (ms), scheduler fairness metric; x86_64 numbers not yet captured (confirmed open per research).

### FS Read/Write Throughput
- [x] **[CLOSED]** NVFS hardening + FAT32 read landed (`harden-nvfs-simpleos` CLOSED 2026-04-24, `fs-opt-general` CLOSED 2026-05-23). — verified src/os/services/fat32/fat32_filesystem_ops.spl:242 `me fn read(handle: u64, size: u64) -> Result<[u8], text>` (and :498 `fn readdir`), with the NVFS service tree at src/os/services/nvfs/{core,driver,posix}
  - divergence: the "allocator" third of this box is NOT re-verified here — only the FAT32 read path and the NVFS service tree were confirmed.
- [ ] **[CLOSED]** FS profiling harness waves completed: 9/15 + 11/11 + 12/14 (`fs-hardening-optimization` CLOSED 2026-05-23); 6 pre-existing blockers deferred (documented).
- [ ] **[CLOSED]** MIR optimizer: struct-array-loop improvements; C extern → pure Simple for `rt_bytes_alloc`, `rt_text_to_bytes` (`fs-opt-general` CLOSED).
- [ ] **[OPEN]** `os_fs_sched_bench_spec.spl` measures FAT32 read/write throughput in QEMU x86_64; results vs `doc/10_metrics/fs_driver_vfat_comparison.md` recorded.

### Exec / Spawn Latency
- [ ] **[OPEN]** Process exec and spawn latency measured by `os_fs_sched_bench_spec.spl` in QEMU (x86_64 serial log → `build/os/systest/x86_64.serial.log`).
- [ ] **[OPEN]** QEMU broker session sharing (`qemu-perf-session` OPEN, phase 1-dev in progress) either completed or latency measured without session pooling and delta documented.

### Scheduler Fairness
- [x] **[CLOSED]** Process isolation + scheduler landed (`scheduler-process-isolation` CLOSED 2026-05-20). — verified src/os/kernel/scheduler/scheduler_exec.spl:69 `pub fn _record_exec_user_handoff(entry: u64, sp: u64, ttbr0_root: u64)`
  - divergence: the "no public symbol duplication found" half is NOT re-verified here — `scripts/check/check-api-arch-guard.shs` is not a push-tier row in `config/check/must_check_gates.sdn`, so nothing enforces it.
- [ ] **[OPEN]** Scheduler fairness metric (e.g. max/min CPU share ratio under N workers) measured by `os_fs_sched_bench_spec.spl` in QEMU x86_64; result recorded.

### Cranelift Inlining Gap
- [ ] **[OPEN]** `pure_simple_ctype_perf_gap` (Cranelift AOT no inlining) either resolved or filed as explicit open bug with before/after measurement; OS benchmark results annotated accordingly.

### API/Arch Guard (AC-8)
- [ ] **[OPEN]** `scripts/check/check-api-arch-guard.shs` green for OS/FS public API (`nvfs`, FAT32 driver, scheduler public symbols); snapshot in `doc/08_tracking/api_surface/`.
- [ ] **[OPEN]** `doc/04_architecture/` parity checklist for OS layer reviewed; no unintended arch divergence from `scheduler_process_isolation_duplication_analysis.md`.

### rt_* Reduction (AC-9)
- [ ] **[OPEN]** rt_* count in `src/lib/nogc_async_mut_noalloc/` (baremetal/OS layer, baseline 358 lines) measured; reduction target recorded after sweep.

---

## Cross-Domain Notes

- Ordering: AC-6 requires all language/compiler (sections 1–2) items complete before per-app (sections 3–6) optimization begins. The checklist ordering here reflects that sequence.
- Contract test for cross-language report shape: `test/05_perf/profile_scripts/profile_report_contract_test.shs` must stay green after every harness run.
- Arch extensibility: all new benchmark specs must carry `skip(architectures:[], tags:[])` decorator; arm/riscv columns added without copy-paste per AC-3.
- Doc locations: dated runs → `doc/09_report/perf/`; persistent tables → `doc/10_metrics/perf/`; API snapshots → `doc/08_tracking/api_surface/`.

## Acceptance

Runnable oracles for the remaining open boxes: `test/03_system/plan_acceptance/perf_checklists_spec.spl`
(tagged `@tag:in-development`; one `it` per open box — see
`doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).
