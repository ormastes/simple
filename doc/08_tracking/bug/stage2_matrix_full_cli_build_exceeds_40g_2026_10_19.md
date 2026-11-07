# Stage 2 matrix full-CLI build peaks above 40 GiB in MIR

- Status: verification-pending (re-scoped 2026-11-05, see end)
- Date: 2026-10-19
- Platform: aarch64-unknown-linux-gnu, 121 GiB host
- Blocks: `stage2-compiler-tests` `compiler_cli_build` under the lane's 40 GiB
  systemd scope (MemoryMax=40G, MemorySwapMax=0).

## Observation

With the HIR fixes 267d9e15084 / c030d481171 / 534a2b3e380 the Stage 2
compiler (sha256 `552150e76c3d73c5a50d83a21d18c283758c7d2bd666de8e23890c7ea95d15d8`)
for the first time lowered all 2702 full-CLI modules through HIR with no
worker crash (worker + main HIR ~38 min). It then entered MIR lowering
(`[mir-lower] WARNING: struct/class name ... re-registered with a DIFFERENT
field list` for FileStat, Task, CostEstimate, JoinPoint, Dependency) and the
process tree grew to `peak_rss_kib=41814840` before the scope's OOM killer
fired (`campaign_interrupted status=143`, journal: `oom-kill`). The task's
own ceiling is 50331648 KiB, so the bootstrap would have allowed it.

Run r8, `.simple/storage/build/bootstrap-r8/stage2-compiler-tests/
aarch64-unknown-linux-gnu/verification/campaign.*/process.env`.

## Not yet established

Whether MIR retention for the full CLI is bounded below 48 GiB at all (a
sibling lane recorded an 83 GiB MIR retention failure).

## Stage 3 (bootstrap_main) shows the same growth

Stage 3 resumed from r8 (`--resume-stage3-from-admitted`, admitted Stage 2
sha256 `552150e7...15d8`, one thread) with the elevated tree cap
`SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=46137344` /
`SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB=52428800`:

| time | RSS (KiB) | HIR modules |
|---|---|---|
| 16:24:27 | 39,517,324 | 653 / 1315 |
| 16:25:27 | 41,106,488 | 688 |
| 16:26:27 | 42,454,456 | 726 |
| 16:27:27 | 43,874,968 | 758 |
| 16:28 (killed) | peak 46,284,808 | 771 (`compiler.semantics.join_point_model`) |

Watchdog verdict `status=rss-containment-unverified`, elapsed 1095 s of HIR.
Growth is ~1.4 GB per 35 modules and linear, so the remaining 544 modules
need roughly +22 GB (~68 GB total before MIR). The coordinator's memory lane
attributes ~14.9 GB of it to `driver_log_typed_hir_abi_interface_v1`
(driver_hir_pipeline_lowering.spl:207), which runs per module only because
`SIMPLE_COMPILER_PHASE_PROFILE=1` is hard-coded into the Stage 3 argv
(resume-stage3-from-admitted.sh:911, stage3-native-build-worker.sh:109) and is
part of the admitted args digest. The default Stage 3 cap (5.86 GB floor)
killed the two earlier attempts at HIR module 32.

## Stage 3 r11 (r8 base + 5bc133fb1c2 ABI-trace opt-in)

Admitted Stage 2 sha256 `70c5d97fa251f3ae0ce0880b01a9d6ae005e979bfc31511eb22e67e4944f6c61`
(Stage 2 build 587 s, peak 2.62 GB). Stage 3 resume with headroom/MemoryHigh
55 GiB, MemoryMax 56 GiB, watchdog cap 54 GiB, ceiling 55 GiB, launched
17:38:20 with 114 GB available:

| time | RSS (KiB) | HIR modules | host avail |
|---|---|---|---|
| 17:46:48 | 19,845,520 | 268 | 94G |
| 17:48:49 | 25,837,032 | 395 | 89G |
| 17:51:49 | 34,234,924 | 528 | 79G |
| 17:54:49 | 40,219,000 | 680 | 71G |
| 17:56:49 | 43,846,508 | 764 | 67G |
| 17:57:49 | 47,958,448 | 805 | 58G |

The live headroom guard stopped it at 17:58:07 at HIR 808/1315
(`runtime_headroom_watch_available_kib=57667656`, unit memory peak 47.1G,
23 min 38 s CPU). Slope ~57 MB/module, the same as the r8 run without the
ABI-trace change. Host availability fell ~7 GB faster than Stage 3's own RSS
because two `native-build` processes from another lane (PIDs 449611, 449861,
~11 GB together, started 17:54 using this run's Stage 2 binary) ran
concurrently. Projected full-HIR RSS at this slope: ~78 GB.

**Revalidated 2026-11-02: still plausible because the report title (Stage 2 matrix full-CLI build peaks above 40 GiB in MIR lowering (41.8 GiB) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 retention audit (mem-mir-retention): fix-implemented-verification-pending

Audited process-global datasets in `src/compiler/50.mir` and `80.driver`.
- The `_bootstrap_fn_*` registries (`mir_data.spl`) accumulate across modules by
  design (cross-module callee types) and are already owned by BuildSession end
  (`build_session_end_reset_globals_v1`, BSM P6). Re-registration is idempotent,
  so they track DISTINCT names, not modules. Their census
  `bootstrap_fn_registries_entry_count_v1` only counted 7 of 20 registries; it
  now counts all, so the budget spec can see a leak in any of them.
- `driver_hir_cache.spl` `hir_closure_all_neutral` / `hir_source_text_hash_cache`
  were digest-keyed with no bound and no reset (grow per edit in LSP/MCP/watch
  processes). Now count-bounded at `HIR_CACHE_SIDE_TABLE_MAX_ENTRIES_V1` (16384,
  ~2.5 MB each); overflow drops the table (pure recompute caches).
- Budget spec: `test/01_unit/compiler/80.driver/build_global_retention_budget_spec.spl`.
- NOT fixed here (needs stage3 to measure/verify): the dominant term in this
  bug, the full MIR set resident through codegen for output format `Both`
  (`driver_aot_pipeline.spl:492`), plus the ~29 GB codegen growth. Repro: stage3
  `native-build --mode dynload` on the full CLI, watch `[mir] rss_mib`; launch
  workaround in `stage2_whole_program_mir_memory_growth_2026-11-01.md`.
- Unbounded-but-small siblings left (session-keyed, no per-edit growth):
  `BITFIELD_REGISTRY`, `_smf_cached_modules`, `_bootstrap_llvm_*_key_*`,
  `_g_entry_scan_*` (has reset), `_bootstrap_type_runtime_names` (has reset).

## Re-scope 2026-11-05 (p1c-s240g, code reading; no full-CLI build run)

No full-CLI build was run (host memory guard: another 70 GB build live).
Findings against base `origin/release/1.0.0` @ 27e65c24371:

1. **The measured growth is not in MIR.** Both the r8 Stage 3 table and the
   r11 table above grow linearly (~57 MB/module) during **HIR**, before MIR
   starts. The title's "in MIR lowering" attribution is only the r8 Stage 2
   observation that the kill landed after MIR began.
2. **The retention paths have since been rebuilt under the BuildSession
   model** (BuildSession owns build data, bounded global caches):
   - cfef5e4eec0 (BSM P2): session-owned `BootstrapHirStore`, removes the
     O(N^2) `promote_last`.
   - f1e2edad6c7 (BSM P3): session-owned bootstrap MIR registries, staged
     rows published per module scope.
   - e587b09a884 / ed2581b83d3 / 88bc2edede3 / d05dc7079db: MIR transient
     scope promotes only the declared owner inventory; the per-module arena
     is reclaimed (`lower_module` docstring, module_lowering.spl ~2350).
   - eb60c43c224: count-bounded HIR cache side tables + retention budget spec.
   - 7c959393f02 / 4898f95a5c9: import-closure-only HIR for MIR shard /
     file-worker children.
   - Staged native codegen (`SIMPLE_NATIVE_STAGED_CODEGEN_BATCH`, bootstrap
     default 32) evicts each flushed batch's MIR
     (`driver_aot_pipeline.spl:636 evict_mir_modules`), so `ctx.mir_modules`
     no longer holds the whole closure on the bootstrap lane.
3. **Newer measurement contradicts the 40 GiB HIR slope:** bug
   `stage2_compiler_cli_build_rss_cap_after_hir_poison_retry_2026-11-04`
   records Stage 2 `compiler_cli_build` lowering **all 3020 modules through
   HIR under a 12 GiB tree cap** (macOS M4). Its RSS kill came from an
   in-process HIR retry after a compile-error poison, fixed there. f6f000233c8
   (2026-11-05) re-prices the Stage 2 compiler-tests cap per full-CLI worker.
4. Only residual retention found by reading: `lower_emit_fn_values`
   (module_lowering.spl ~3573) keeps the previous module's
   `HirFunction` list alive until the next module overwrites it. This is
   bounded to ONE module, so it cannot explain tens of GiB; it was left as is.

**Remaining to close:** a MIR-phase peak RSS for the full-CLI closure on the
next sanctioned Stage 2 rerun (s2d). Close this bug as fixed if that peak is
under 40 GiB. If it is not, reopen it with `SIMPLE_PHASE_RSS=1` per-phase
attribution.

## 2026-11-07 note (lane r14-bootstrap-mem): Windows MSVC Stage 2 seed native-build measured

Different term from the full-CLI MIR rows above; recorded here because the
owner's "Stage 2 keeps being killed" report (boot2 lane,
`bootstrap-windows.sh --msvc --full-bootstrap --keep-going --jobs=min
--stop-after-stage2`) resolves to this stage.

- **What both boot2 logs actually say:** `exit=1 signal=none`, cause
  `driver_aot_pipeline.spl: timeout (300s)` then 555 `NOT_ATTEMPTED` from the
  admission latch. No reap/kill/cap line exists in either log.
- **Reproduced the exact Stage 2 argv** (boot2 runtime-authority seed, copy of
  its cache, `--threads 1`) under a 2 s PeakWorkingSet sampler: peak
  **1.62-1.66 GB** WS on a host with ~3.8 GB free. `driver_aot_pipeline.spl`
  compiled in 30.7 s (run 1) and 105 s (run 2) of CPU — same binary, same
  inputs, cpu ~= wall both times. The 300 s abort is host-load inflation of
  CPU cost, not a stall and not memory; `SIMPLE_NATIVE_FILE_TIMEOUT` (opt-in,
  pinned into the Stage 2 argv) is the lever; the retry path reuses the same
  timeout so it fails identically.
- **Dominant memory term found and fixed:** after `build_import_map` the
  tracked heap is 67 MB while the process holds 1.12 GB WS / 1.33 GB private.
  The parallel parse allocates every closure AST on the rayon worker and the
  builder thread frees them cross-thread; mimalloc parks those frees on the
  idle worker's pages. Fix: `mem_trace::release_thread_heap` broadcast to the
  pool + caller right after the import map. BEFORE -> AFTER on the same argv:
  after-import-map WS 1,122 -> 188 MB; before-compile 1,352 -> 340 MB;
  compile-phase max 1,656 -> 619 MB; whole-run peak 1,659 -> 1,123 MB (the
  remaining peak is the parse transient while all 1,598 ASTs are live).
- **Not a term here:** per-file tracked heap stays 290-412 MB across 32 files
  (no Rust-side ratchet); `--jobs=min` already yields 1 job / `--threads 1` /
  `workers: 1`, so admission is already serialised on Windows.
## 2026-11-07 Phase-4 q0019 / q0021 (mem-p4cap, evidence; no code change)

Jobs (s4e queue, `C:/dev/p3new/s4/out/s4e_q/<id>`, binary
`s3_fable57s_p4.exe`, 24,489,472 bytes, built 2026-11-07 08:30 +0900):

| job | MIR shards planned | first obj | objs | peak tree | verdict |
|---|---|---|---|---|---|
| q0021 (L2 08:46) | 2 | 688.8 s | 5 | 16.35 GB | killed at cap 16 |
| q0019 (L2 10:29) | 1 | none | 0 | 24.37 GB | killed (cap/commit) |

Both `native-build.log.err` files print
`[mir-shard] disabled: output format re-reads MIR set`. The command
(`fable_s4e_build.ps1`: `native-build --entry-closure ... -o simple_s4.exe`)
selects `OutputFormat.Both`. On `origin/release/1.0.0` Both no longer refuses
(728ddb0170f + 5a45cad0d94, 2026-11-02: per-module SMF parts,
`smf_staged_output_format_refusal_v1` refuses only SMF / self-contained). The
binary lacks that fix: it contains no `MIR shard SMF part` string (the error
text 5a45cad0d94 added), so its baked source predates 2026-11-02. With the
refusal, the whole MIR closure stays in `ctx.mir_modules` through codegen,
the term this bug already names as dominant.

Root cause for these jobs: a stale stage3 producer, not a new retention path
in source. Nothing to change in `src/` for it.

Second gap (harness, not product): `fable_s4e_build.ps1` does not set
`SIMPLE_NATIVE_STAGED_CODEGEN_BATCH`, and its default is 0 (off) outside the
bootstrap scripts (`native_staged_codegen_batch_size_v1`). With `shards=1`
(q0019) nothing evicts MIR even on a fixed binary. Phase-4 runs should set
`SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=32`, like the bootstrap lane.

Required check to close: on the next stage3 built from source that includes
728ddb0170f (Fable owns stage3 builds), rerun q0019 and q0021 with
`SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=32` under cap 16. Pass = no
`[mir-shard] disabled` line and peak tree RSS under 16 GB. Record the
before/after peak and wall time here.
