# Feature Expert: Memory Analysis Infra (M1-M8)

## What this is
Backend-agnostic memory-analysis/hardening infra covering all four Simple
allocator models (malloc-backed nogc, GC tier, index-based arenas/slotmaps,
static pools) through one instrumentation shape (alloc/free/owner/bytes),
gated `OFF` by default. Successor to the stage-4 L1-L7 lanes (shared
foundation: CowEnv dirty-tracking, byte-level heap counters — see
`.spipe/stage4_memory_harden/state.md`). Four layers:
1. **Counters/attribution (M1)** — per-owner byte accounting keyed on
   `CURRENT_EXEC_MODULE`.
2. **Harden/guard (M2)** — GWP-ASan-style sampled guard pages + Zig-GPA-style
   quarantine/poison, plus the arena-generation harden extension.
3. **`--mem-infra=` interface (M3)** — capability-matrix resolver
   (backend x allocator-model), envs are the load-bearing mechanism today,
   CLI flag is a planned alias.
4. **`simple mem` CLI (M8)** — post-mortem snapshot inspection
   (top/diff/help), SIGUSR2 live-dump prep.

## Source of truth
- Research (gap vs Rust ecosystem, tool survey): `doc/01_research/runtime/memory_analysis/memory_infra_gap_and_tools_2026-07-29.md`
- Plan (M1-M8 scope, cross-cutting rules, overhead measurements): `doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`
- Design: `doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md`,
  `doc/05_design/runtime/memory_analysis/gc_gpu_instrumentation_design.md` (M7 + GC verdict),
  `doc/05_design/compiler/interpreter/m5_strict_interpreter_mode_design.md`,
  `doc/05_design/app/mem_cli/m8_simple_mem_cli_design.md`
- Predecessor research: `doc/01_research/compiler/bootstrap/stage4_memory_ownership_research_2026-07-29.md`
- Requirements: `doc/02_requirements/runtime/memory_analysis/feature_per_owner_allocation_attribution.md`,
  `feature_backend_memory_infra_toggle.md`, `feature_simple_mem_cli.md`

## Code map
| File | Role |
|---|---|
| `src/compiler_rust/runtime/src/value/heap.rs` | Heap-registry choke point; M1 `note_attr_alloc`/`note_attr_free`/`set_current_owner`, `ATTR_ENABLED: OnceLock<bool>`, `rt_heap_top_owners`, `rt_mem_attr_set_owner` (JIT text-arg fix, `(ptr,len)` span not C-string — see Landmines) |
| `src/compiler_rust/compiler/src/interpreter_extern/memory.rs` | Hosted `rt_alloc`/`rt_free`; M2 quarantine ring (256 slots/1 MiB, `SIMPLE_MEM_HARDEN=1`, 0xDE poison-on-free, `rt_mem_harden_check` write-after-free detector) |
| `src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs` | M2 sampled guard-page allocator (`SIMPLE_MEM_GUARD_RATE=N`, mmap + `PROT_NONE` on free, right-align overflow placement, owner recorded per slot from M1, `rt_mem_guard_stats`) |
| `src/compiler/10.frontend/core/_AstExpr/nodes.spl` | L6/M2 arena-generation counter: `ast_gen_slot`, `ast_generation_bump()`, `ast_gen_check_index()` (`SIMPLE_AST_GEN_CHECK=1`, diagnosis-only; `SIMPLE_AST_GEN_HARDEN` is the planned block-on-stale-read upgrade, not yet landed) |
| `src/lib/nogc_sync_mut/mem/gen_arena.spl` | M6 `GenArena<T>` — stdlib generational slotmap (Vale-style); stale handle -> nil after slot reuse; `SIMPLE_GEN_ARENA_CHECK=1` diagnostic |
| `src/lib/nogc_sync_mut/mem/dump.spl` | M8-prep v1 TSV snapshot writer (`KIND`/`OWNER`/`RSS` rows), `SIMPLE_MEM_SNAPSHOT`/`SIMPLE_MEM_DUMP_PATH` |
| `src/lib/nogc_sync_mut/io/signal_handlers.spl` | SIGUSR2 hook added for M8 live-dump trigger |
| `src/lib/common/mem_infra/config.spl` | M3 capability matrix — 7 rows (attr/guard/harden/genarena/strict/asan/memprof) x 3 backends; pure functions only, no env reads, **not yet wired** into CLI/build |
| `src/app/mem/main.spl` | M8 `simple mem` CLI: `top --profile` (post-mortem file mode), `diff`, `help`, and `top --pid <P> [--path F] [--wait-ms N]` (live SIGUSR2 poll of a running process via `src/app/mem/live_poll.spl`, landed `0a4c3f64129` — that file was previously a real orphan, never called from `main.spl`) |
| `src/app/memstat/main.spl` | L5 out-of-process RSS sampler feeding the stage-4 gate |
| `scripts/check/check-stage4-memory-gate.shs` | CI RSS gate over `memstat` output; PASS/FAIL verdict line |

## Env gates
| Env | Layer | Default | Status |
|---|---|---|---|
| `SIMPLE_MEM_ATTR=1` | M1 attribution | off | Landed (b44b07cd2869); +36.6% measured overhead on alloc-heavy probe, target <15%, OPEN for sharding |
| `SIMPLE_MEM_HARDEN=1` | M2 quarantine+poison (hosted); also gates GC-sweep poison | off | Landed hosted path (0917eee9b93d); GC-sweep poison not applicable — GC tier is vestigial (see Known limits) |
| `SIMPLE_MEM_GUARD_RATE=N` | M2 sampled guard pages (hosted) | disabled (unset) | Landed hosted path (0917eee9b93d); native C `rt_alloc` (`runtime_memory.c`) mirror not yet ported |
| `SIMPLE_AST_GEN_CHECK=1` | L6 arena generation diagnostic | off | Landed (stage-4 L6), diagnosis-only |
| `SIMPLE_GEN_ARENA_CHECK=1` | M6 stdlib `GenArena<T>` diagnostic | off | Landed (0917eee9b93d) |
| `SIMPLE_MEM_SNAPSHOT` | L5/M8 snapshot capture trigger | off | Landed (L5 driver line + M8 `dump.spl`) |
| `SIMPLE_STRICT_MEM=1` | M5 Miri-lite interpreter mode | off | **Planned** — design done (`m5_strict_interpreter_mode_design.md`), no implementation yet |

Not requested above but load-bearing today: `SIMPLE_AST_GEN_HARDEN` (M2's
block-on-stale-read extension, planned), `SIMPLE_MEM_QUARANTINE_BYTES` /
`SIMPLE_MEM_ARENA_DELAY_SLOTS` (M2 ring sizing, planned). All gates are a
single `OnceLock<bool>`/module-flag read at first use, never per-alloc — the
plan's "zero-overhead-when-off" hard rule.

## How to verify
```
bin/simple test test/03_system/check/mem_attr_report_spec.spl        # M1: 2/2
bin/simple test test/01_unit/lib/mem/gen_arena_spec.spl              # M6: 5/5
bin/simple test test/01_unit/lib/mem/mem_dump_spec.spl               # M8-prep: 3/3
bin/simple test test/01_unit/compiler/ast_arena_generation_spec.spl  # L6: 5/5
bin/simple test test/01_unit/lib/mem_infra/config_spec.spl           # M3 resolver: 12 its
bin/simple test test/03_system/app/mem_cli_spec.spl                  # M8 CLI: 7/7 (LANDED ef00d5e2094)
cargo test -p simple_compiler interpreter_extern::mem_guard          # M2 guard: 10/0
cargo test -p simple_compiler interpreter_extern::memory             # M2 harden: 7/0
sh scripts/check/check-stage4-memory-gate.shs                        # PASS peak_rss_kb=71048 (observed)
```

## Known limits
- **JIT-vs-interpreter extern marshalling family.** `rt_mem_attr_set_owner`
  was declared `*const c_char` but native codegen passes `text` externs as a
  raw `(ptr, len)` span — same convention as `rt_file_exists`/`rt_env_get` —
  so the JIT engine silently dropped the owner name while the interpreter was
  correct. Fixed (630deb4571ee): `(name_ptr: *const u8, name_len: u64)` +
  `text_arg_indices` entry + `RuntimeFuncSpec` row. **Any new extern that
  takes a `text` argument must follow the span convention, not C-string** —
  see `doc/08_tracking/bug/mem_attr_set_owner_jit_text_arg_dropped_2026-07-29.md`.
  This is one instance of a wider family (native vs interpreter marshalling
  mismatches) — treat every new mem-infra extern as a candidate for the same
  bug class before trusting a JIT-path result.
- **GC tier is vestigial for program values.** Grepping
  `src/compiler_rust/runtime/src` for `mark`/`sweep`/`collect_garbage` finds
  no tracing collector over the runtime's own value heap: `heap.rs`
  tri-color bits are defined but nothing drives a mark phase (objects are
  freed manually, the M1 nogc path); `gc_barrier.rs` is barrier scaffolding
  with no collection cycle; `memory/gc.rs`'s real `abfall` mark-sweep only
  serves the compiler pipeline's own internals, never a program `Value`. The
  GC row of the M1-M8 allocator-model matrix is satisfied trivially, not
  because GC instrumentation was built.
- **LLVM lane (M4) — LANDED 2026-08-06 (was "does not compile").** Both ASan
  (`13348d0fc46`) and memprof (`5029d3feade`) are real: `SIMPLE_MEM_ASAN`/
  `SIMPLE_MEM_MEMPROF` env gates in `codegen/llvm/backend_core.rs`,
  `-fsanitize=address`/`-fmemory-profile` link flags, `--sanitize`/`--memprof`
  and `--mem-infra=asan`/`=memprof` CLI flags. **Pipeline-alias gotcha:** the
  bare `"memprof"` LLVM pass-pipeline alias resolves to FUNCTION-SCOPED ONLY
  on LLVM 18.1.8 (`opt -print-pipeline-passes` shows `function(memprof),
  verify,print` — never emits `memprof.module_ctor`/`__memprof_init`); the
  correct string is `"function(memprof),module(memprof-module)"` explicitly.
  Always ground-truth an LLVM pass-pipeline alias with `opt
  -print-pipeline-passes` before trusting it — the same trap likely applies
  to other single-word aliases (`asan`, `tsan`, `msan`). Still open: the
  plan's full exit bar (memprof profile from a real stage-2 compile) is
  blocked on a separate, pre-existing bug
  (`doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md`)
  — both fixes so far are standalone-fixture-level only, matching M4's own
  original scoping.
- **+36.6% ON cost, M1 attribution, measured pre-any-lock-sharding.** The
  `SIMPLE_MEM_ATTR=1` path takes one global `Mutex<HashMap>` lock per heap
  alloc/free; on an allocation-heavy probe (90k-element array push+sum) the
  in-process median went 1302.5ms -> 1779.5ms (wall-clock: +31%). This is a
  real, allocation-rate-proportional cost, not a rounding error — documented
  as such rather than "small". OFF path is a single cached bool read (no
  lock/map ever touched) and is indistinguishable from a clean-env baseline.
  No sharded/lock-free map has been built; if a lower-overhead ON path is
  needed later, sharding the global lock/map is the first place to look.
  **Current status: OPEN ITEM, target <15% still unmet.**
- **Memory-extern parity incomplete in seed interpreter.** Three externs —
  `rt_mem_attr_enabled`, `rt_mem_guard_stats`, `rt_mem_harden_check` — log
  'unknown extern function' and silently return 0 when called from interpreted
  code in the Rust seed. Pure-Simple interpreter has these defined correctly.
  **Current status: OPEN ITEM, seed interpreter missing wiring for three
  mem-infra externs.**

- **Signal-callback context under the interpreter only resolves `rt_`/`spl_`-
  prefixed externs.** Found wiring M8 live-poll's SIGUSR2 handler
  (`src/lib/nogc_sync_mut/mem/dump.spl`): calling a bare-named function like
  `memory_usage()` from inside a signal callback crashes with `unknown
  extern function` because `rt_interp_call` (the signal-dispatch path) only
  resolves `rt_`/`spl_`-prefixed names. Split into an RSS-free variant
  (`mem_dump_tsv_no_rss()`) for the signal path; the ordinary
  `simple mem snapshot` command still gets the real RSS row. Also:
  `use std.io_runtime.{thread_sleep}` silently fails to resolve under the
  interpreter (the `io_runtime.spl` shim doesn't re-export it) — import from
  `std.nogc_sync_mut.io_runtime` directly instead.

## Update Rule
When a new M-phase lands, gains a design doc, or an env gate's status
changes, update the Code map / Env gates / Known limits tables above and the
`## M-plan status` section in `.spipe/stage4_memory_harden/state.md` in the
same change.

## Measured peak RSS of the compiler itself (2026-08-23)

Seed `f6521b60b67d…` (60,650,360 B), box 32 CPU / load 16–30. Full data:
`doc/10_metrics/perf/compiler_peak_rss_and_throughput_2026-08-23.md`.

| workload | peak RSS | note |
|---|---|---|
| 3-line hello, `compile` | 29.7 MB | 0.15 s median |
| 807-module closure, `compile` | 1.55 GiB | flat at 1571 MB for the last 62 % of the run — nothing released |
| `native-build` worker (`simple run native_build_worker.spl`) | **2.66–2.77 GiB, still climbing at ~40 MB/s** | 953 MB (25 %) from the ~3.7 GiB earlyoom kill; ~24 s to kill at that rate |

Three things to know before measuring memory here:

1. **`native-build` is multi-process.** The parent sits at 54 MB flat; the
   memory is in `simple run src/app/cli/native_build_worker.spl` children. A
   parent-only sampler (or bare `/usr/bin/time -v` on the parent) reports 54 MB
   and is wrong by ~50x. Sample by matching `/proc/*/exe` against your binary's
   absolute path — pgid/setsid sampling was tried and lost the children.
2. **rc=137 / rc=143 here is an earlyoom SIGKILL, not a compiler crash.**
   `simple` is the designated victim at ~3.7 GiB. Log MemAvailable at exit
   before classifying anything as a crash.
3. **Freeze your binary.** Other lanes replace `bin/simple`'s symlink target
   mid-session. Copy the binary into your own worktree and cite its sha256.

The dominant known term is `IMPORTED_MODULE_AST`
(`src/compiler_rust/compiler/src/hir/lower/import_loader.rs:33`): an
`Arc<Module>` per imported path, retained for the process lifetime, cleared only
by the global `clear_module_cache` — never at end-of-lowering. **Do not "fix" it
by deleting the memo**; it is a landed fix for a real 112x *re-parse* defect and
is pinned by parse count. The open question is its retention lifetime. Bug:
`doc/08_tracking/bug/native_build_worker_rss_unbounded_953mb_from_oom_kill_2026-08-23.md`.
