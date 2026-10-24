# HIR shard coordinator SIGBUS (signal 10) at ~6-8 GB RSS on macOS aarch64: per-crash attribution of 37 deaths in the phase-3 self-host build

Date: 2026-10-24
Lane: phase-3 self-host (admitted stage2 compiler building the full Simple CLI, 2934 modules)
Tree: rr1000-boot worktree @ 9a79de084e99 (branch base release/1.0.0, live build; this doc committed from a temp worktree at origin/release/1.0.0 @ 98e0ef74ccd)
Log: /Users/ormastes/p3-lane/phase3-1000b.log (grew during analysis; all line numbers as of 2026-10-24)

## Symptom

The phase-3 build's single HIR shard worker (`owner=0/1@N`) is killed by
**SIGBUS (exit=-138, i.e. signal 10)** once per wrapper-respawned life, always
inside the `hir` phase. 37 crashes observed (`@0`..`@36`) over ~5 h; a
wrapper respawns the whole native-build each time and a persistent hir-cache
makes forward progress monotonic: each life adopts all previously sealed HIR
entries, then the worker claims the remaining uncached modules and dies with
`claimed=N sealed=1 finished=false`. Representative line:

```
[hir-shard] owner=0/1@22 status=CRASH exit=-138 claimed=249 sealed=1 finished=false
```

- `exit=-138` is WIFSIGNALED, signal 10 = SIGBUS. It is **not** the RSS
  watchdog (which kills with KILL → -137; see
  scripts/resource/process-tree-rss-watchdog.pl `kill 'KILL'` at lines 492/672)
  and not an allocator abort (SIGABRT → -134). The worker faults on its own at
  RSS ≈ 6-8 GB on a 24 GB box under heavy background load. No `.ips`/crash
  report was captured by the wrapper — that is the missing evidence for the
  exact faulting mapping (see Fix leads, item 4).
- Each life re-runs the full front-end (`load_sources → source_closure →
  parse → surface_build → surface_alias → export_origins → surface_freeze →
  parse → hir`) and takes ~8-9 min wall (~480-550 s life total per
  `elapsed_ms` at each crash); the hir phase itself is short (seconds to ~70 s
  by the log's own clock) because cache adoption is nearly instant and the
  death follows the first genuinely-uncached giant module.

## Per-crash table

`done` = the parent build's hir counter in the last `[build] phase=hir`
progress line before the crash line (the log interleaves two writers — the
parent build and the shard worker — so this is the parent's view; both
counters reset to 0 at every hir phase start, verified for all 37 lives, so
`done` = modules completed in that life). `claimed`/`sealed` are from the
`[hir-shard] status=CRASH` line itself (`claimed` = the owner's `.claim` rows;
`sealed` = claims closed by the coordinator at reap,
driver_hir_recovery.spl:57-72 — sealed=1 every time means exactly one
in-flight claim, the dying module, was terminal-marked by the coordinator).

| crash @N | log line | last `current=` module | done (life) | claimed | sealed |
|---|---|---|---|---|---|
| @0  | 25495  | lib.common.ui.action | 1290 | 212 | 1 |
| @1  | 38738  | lib.gc_async_mut.gpu.engine2d.backend | 1300 | 2 | 1 |
| @2  | 52157  | compiler.backend.feature_caps_types | 1716 | 84 | 1 |
| @3  | 65447  | lib.common.ui.ui_frame_clock | 1877 | 24 | 1 |
| @4  | 78720  | lib.common.ui.compositor_backend_core | 1962 | 16 | 1 |
| @5  | 92010  | lib.common.binary_io | 2120 | 24 | 1 |
| @6  | 105258 | lib.nogc_sync_mut.fs_driver.block_device | 2139 | 4 | 1 |
| @7  | 118555 | lib.nogc_async_mut.gpu.engine2d.backend | 2331 | 27 | 1 |
| @8  | 131795 | lib.gc_async_mut.gpu.engine2d.framebuffer_surface | 2334 | 1 | 1 |
| @9  | 145035 | lib.gc_async_mut.gpu.engine2d.virtio_gpu_surface | 2335 | 1 | 1 |
| @10 | 158298 | lib.nogc_sync_mut.gpu.engine2d.backend_session | 2377 | 11 | 1 |
| @11 | 171644 | lib.nogc_sync_mut.gpu.engine2d.simd_provider | 2654 | 128 | 1 |
| @12 | 185171 | lib.common.io.traits | 1088 | 129 | 1 |
| @13 | 198539 | compiler.backend.feature_caps_arch32 | 1717 | 56 | 1 |
| @14 | 211784 | lib.nogc_sync_mut.src.hash | 1785 | 2 | 1 |
| @15 | 225080 | compiler.common.cache_contract.virtual_source_store_v1 | 2102 | 25 | 1 |
| @16 | 238622 | lib.nogc_sync_mut.io.udp | 1790 | 128 | 1 |
| @17 | 251887 | compiler.common.cache_contract.cache_gateway_v1 | 2101 | 12 | 1 |
| @18 | 265293 | compiler.blocks.definition | 1803 | 73 | 1 |
| @19 | 278707 | compiler.blocks.builtin_blocks_math | 2606 | 72 | 1 |
| @20 | 291947 | compiler.blocks.builtin_blocks_shell | 2607 | 1 | 1 |
| @21 | 305187 | compiler.blocks.builtin_blocks_data | 2608 | 1 | 1 |
| @22 | 319202 | compiler.backend.codegen_types | 313 | 249 | 1 |
| @23 | 332442 | compiler.backend.static_backend_registry | 314 | 1 | 1 |
| @24 | 345683 | compiler.backend.backend_port | 315 | 1 | 1 |
| @25 | 359000 | lib.common.encoding.external_text | 345 | 28 | 1 |
| @26 | 372256 | app.io.env_access_host | 357 | 7 | 1 |
| @27 | 385574 | compiler.mir_opt.mod | 402 | 28 | 1 |
| @28 | 399712 | os.compositor.host_compositor_core | 717 | 208 | 1 |
| @29 | 412973 | lib.nogc_sync_mut.io.pipe | 730 | 10 | 1 |
| @30 | 426293 | lib.nogc_sync_mut.io.tcp | 784 | 37 | 1 |
| @31 | 439609 | plugins.backend_llvm_lib.llvm_lib_backend | 843 | 36 | 1 |
| @32 | 452849 | plugins.backend_c.c_codegen_adapter | 844 | 1 | 1 |
| @33 | 466089 | compiler.backend.wasm_codegen_adapter | 845 | 1 | 1 |
| @34 | 479329 | plugins.backend_native.native_codegen_adapter | 846 | 1 | 1 |
| @35 | 492569 | plugins.backend_hip.hip_backend | 847 | 1 | 1 |
| @36 | 505809 | plugins.backend_opencl.opencl_backend | 848 | 1 | 1 |

(@36 crashed while this doc was being written; the build is still running.)

## Repeat offenders

**No single module repeats exactly** across the 37 crashes. The deaths cluster
by neighborhood, which is the actual signal: the worker dies when cumulative
RSS crosses the ~6-8 GB line, whichever giant module is current when the queue
reaches it:

- `*.gpu.engine2d.*` cluster — 6 crashes (@1, @7, @8, @9, @10, @11; three
  different owners: gc_async_mut, nogc_async_mut, nogc_sync_mut).
- `plugins.backend_*` / `compiler.backend.*_adapter` cluster — 9 crashes
  (@2, @13, @22, @23, @24, @31, @32, @33, @34, @35, @36): llvm_lib, c_codegen,
  wasm, native, hip, opencl adapters fire one-per-life at the end
  (@31-@36 are literally one module per life, `claimed=1` each).
- `compiler.blocks.builtin_blocks_*` — 4 (@18-@21), `lib.common.*` — 6
  (@0, @3, @4, @5, @12, @25), `lib.nogc_sync_mut.*` — 7 (@6, @10, @11, @14,
  @16, @29, @30).

The `claimed=1` lives (@8, @9, @20, @21, @23, @24, @32-@36) are the tell: by
then the parent had adopted everything else from the hir-cache, the worker
claimed exactly one remaining uncached giant module, and died on it. The crash
boundary drifts between lives because cache adoption/selfcheck churn moves the
starting point, not because the modules differ in kind.

Corroborating cache churn in the same log: 200 `[hir-cache] SELFCHECK FAILED`
lines and 24 `[hir-cache-store] refused reason=unstable` lines — a large
fraction of attempted stores are refused or invalidated, so the same giant
modules keep needing real re-lowering, and each re-lowering is a fresh RSS
peak on top of an already-large process.

## What the budget code actually does (root cause of why the deaths recur)

The HIR worker memory budget is **only a shard-fanout selector; it never caps
aggregate or per-worker RSS**, and on this build it is floored at the parent's
own peak, so admission can never reject the workload:

1. `native_build_hir_shard_count` (src/app/cli/native_build_main.spl:780-802)
   measures the parent's peak RSS immediately before HIR admission
   (`process_peak_rss_kb()`, line 794) and passes it as a floor:
   `shard_worker_budget_kb("SIMPLE_HIR_SHARD_WORKER_KB", 3000000, parent_peak)`
   (line 798). Log: `[hir-shard] admission estimate=8557696 kB historical
   parent peak=8557696 kB` ≈ 8.16 GiB — the parent peaks at 8.16 GB during
   the *front-end* phases, before HIR even starts.
2. `shard_worker_budget_kb` floors the budget at the parent peak:
   `shard_host_budget_floor_kb(parent_peak_kb, chosen)` —
   src/app/cli/shard_mem_clamp.spl:87-98.
3. `shard_threads_parent_cap_for` (shard_mem_clamp.spl:177-190) then computes
   `reserve = max(parent_peak, 40% of tree); slots = (tree - reserve) /
   budget`. With budget == parent peak == 8.16 GiB, a tree budget in the
   ~16-20 GB range admits exactly **1** shard — matching `owner=0/1` in every
   crash line. The code comment says this outright (shard_mem_clamp.spl:
   172-176): "Its retained high-water mark is a workload-sensitive estimate
   floor, **not a future RSS bound** … A known tree that cannot fit one
   estimate admits no HIR child."
4. The single admitted worker then re-runs the same producer closure as the
   supervisor — "Each HIR shard child runs the real pipeline through parse …
   and the surface freeze, then lowers ONLY the modules it claims"
   (native_build_main.spl:771-773) — so it pays the parent's 8.16 GB
   front-end replay as its *baseline* and grows from there during HIR
   lowering, crossing the ~6-8 GB fault line (measured under load, where the
   machine-level pressure lands lower than the tree cap) within seconds to a
   minute of real lowering.

So: the budget caps nothing, and external config cannot fix this instance —
`SIMPLE_HIR_SHARD_WORKER_KB`/`SIMPLE_SHARD_MEM_CLAMP`/`SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB`
can only lower fanout (already 1) or refuse to start; none of them prevent a
single worker from re-approaching the parent peak, and the watchdog is not
what is killing the worker (SIGBUS ≠ SIGKILL).

## Fix leads (for a follow-up lane)

1. **Stop replaying the full front-end inside the HIR shard worker**
   (primary, code-level). The child re-parses and re-freezes all 4333 surfaces
   before claiming (native_build_main.spl:771-773); that replay is ~7.5 of the
   ~8.6 min per life and produces the 8.16 GB baseline the budget then floors
   against. If the worker could hydrate the parent's already-frozen surface
   snapshot instead of re-deriving it, both its baseline RSS and the
   `parent_peak` floor would drop sharply.
2. **Remove or re-think the parent-peak budget floor**
   (shard_mem_clamp.spl:98, called from native_build_main.spl:798). Flooring
   the per-worker estimate at the supervisor's historical peak bakes
   "one worker may consume the entire parent peak" into admission and
   guarantees `slots ≤ 1` on any tree that must also hold the parent. A
   deliberate override (`SIMPLE_HIR_SHARD_WORKER_KB`) already exists for the
   case where the floor is genuinely wanted.
3. **Mid-life flush of retained phase-wide accumulators.** Per-module
   reclamation already exists — the shard transaction rolls back flat HIR rows
   and reclaims the reverse-reference parse scope per module
   (driver_hir_pipeline_lowering.spl:932-962, esp. `rollback_flat_hir_row_or_abort`
   at :959) and retains only receipts. What survives across all ~200 claimed
   modules of a life are the promoted phase memos and frontend owners
   (`promote_phase_memo_transient_owners` :947,
   `driver_promote_retained_frontend_owners_v1` :949). A periodic
   memo/registry reset between claims (or spilling the retained flat HIR store
   to the sealed cache between modules) would cap intra-life growth. This is a
   smaller lever than (1) because the dominant term is the front-end replay
   baseline, not per-module retention.
4. **Capture the macOS fault itself.** SIGBUS at high RSS on macOS aarch64 is
   most often a fault on a specific mapping (file-backed cache mapping
   invalidated by a concurrent rewrite — plausible here given the hir-cache
   selfcheck/store churn in the same directory — or an allocator mmap edge
   under pressure), not generic OOM. Have the respawn wrapper preserve
   `~/Library/Logs/DiagnosticReports/*.ips` for the worker PID (or run the
   worker under `lldb -b -k` symbolication); without the faulting address and
   mapped-file identity, (1)-(3) are informed but unproven.

Also worth attention in the same lane: the cache-admission churn (200
SELFCHECK FAILED + 24 unstable-store refusals in one log) — even with lower
RSS, refused stores keep giant modules uncached and re-lowered, which is what
places a giant module at the crash boundary every life.
