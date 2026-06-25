# Interpreter + Compiler Performance Research
**Domain:** Simple interpreter/compiler on x86_64
**Date:** 2026-06-13

---

## Related Code (paths)

| What | Path |
|------|------|
| Interpreter eval (Rust seed) | `src/compiler_rust/compiler/src/interpreter_eval.rs` (1494 lines) |
| Value enum (Rust seed) | `src/compiler_rust/compiler/src/value.rs:853` — `Value::Str(String)` (780 callsites) |
| Extern dispatch | `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:46` — `OnceLock<HashMap>` |
| Debug state | `src/compiler_rust/compiler/src/interpreter_debug.rs` — `static DEBUG_MODE: AtomicBool` |
| Expression router | `src/compiler_rust/compiler/src/interpreter_eval.rs` — `route_expr` fn (IMPLEMENTING) |
| MIR opt passes | `src/compiler/60.mir_opt/optimization_passes.spl` |
| MIR rule engine | `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl` |
| SMF dynlib | `src/os/smf/dynsmf_session.spl` |
| SMF autoload | `src/app/startup/dynsmf_autoload.spl` |
| Module loader | `src/compiler/99.loader/loader/module_loader.spl:432-433,515` |
| Mimalloc (pure Simple) | `src/lib/nogc_sync_mut/mimalloc.spl` |
| Linker wrapper | `mold` — `find_mold_path()` picks `bin/mold/mold` first |

---

## Reusable Infra

| Tool | Command / Path |
|------|---------------|
| Cross-lang benchmark | `sh scripts/check/check-cross-language-perf.shs` — fib35, cold start, RSS, fanout vs bun/python/go/erlang/java/C |
| Size/startup audit | `sh scripts/check/check-startup-size-performance-audit.shs` |
| Perf guide | `doc/07_guide/compiler/check_perf.md` |
| TL;DR | `doc/07_guide/compiler/check_perf_tldr.md` |
| Perf spec suite | `test/05_perf/` — `compiler_perf_baseline_spec.spl`, `method_dispatch_bench.spl`, `bytes_push_1mib.spl`, `http_server/`, `bench/` |
| Interp perf spec | `test/01_unit/app/interpreter/perf_spec.spl` |
| Tiered JIT spec | `test/01_unit/compiler/interpreter/tiered_jit_hotspot_spec.spl` |

Cross-lang script measures: binary size, cold startup, warm throughput (in-process loops, JIT steady-state), OS-thread + green-thread + multicore-green workers, large fanout scheduling. Modes: `simple file.spl` (interp), `simple .smf` (SMF loader), `./binary` (native AOT).

---

## In-flight / Done

| Task | State | Key facts |
|------|-------|-----------|
| `interpreter-perf-gaps` | CLOSED 2026-05-20 (2 items remain) | debug_state→AtomicBool (DONE 51c85da213); extern dispatch→HashMap OnceLock (DONE fca3f29b05); expr cascade→`route_expr` (IMPLEMENTING, e533e54c0b); Value::Str→Arc<str> (DEFERRED 780 callsites); diagram_sffi SeqCst fix (Wave 11 DONE); watchdog flag ordering (Wave 12 DONE); string concat alloc (Wave 13 DONE); CowEnv iterator alloc (Wave 14 DONE); Unicode fast-path (Wave 15 DONE) |
| `mimalloc-interp-perf` | CLOSED 2026-05-20 | Pure-Simple mimalloc in `src/lib/nogc_sync_mut/mimalloc.spl`; OS kernel heap delegated; `MimallocAllocator` implements `Allocator` trait |
| `mold-mimalloc-default` | CLOSED 2026-05-20 | mold unconditionally first-choice linker; `bin/mold/mold` install script; mimalloc kernel heap wired |
| `bootstrap-speed-opt` | CLOSED 2026-05-20 | Rayon parallelism tuning for bootstrap pipeline |
| `compiler_jit_lowering_fix` | implement-done 2026-06-13 | Root cause at `stmt_lowering.rs:606`; nested `fn` not lowered; 10-15ms improvement; sprof→JitHotspotPlan bridge added (AC-3) |
| `compiler_perf_codegen` | implement-done 2026-06-13 | Win 2 (SMF runtime replacement) pre-existing; Win 3 (profile-guided bridge — sprof→JIT facts) IMPLEMENTED; riscv64+arm64 codegen specs added; check clean |
| `general-mir-bulk-ops` | phase 1-dev DONE, 2-8 OPEN | bulk_copy/fill/cmp/endian_load/endian_store recognizer passes in `optimization_passes.spl`; not yet implemented (phase 2+ pending) |

**AC-7 gap (SMF cache):** `dynsmf_session_queue_missing_background_compiles` queues background compile when artifact is missing; `dynsmf_session_autoload_checked` loads existing SMF. BUT: NO content-hash check exists — unchanged source is not detected to skip re-compile. The `dynsmf_background_compile_action` path only checks `rt_file_exists(entry.path)` (artifact exists → skip). Source hash comparison is absent — AC-7 is PARTIALLY met (background compile queue exists) but cache-reuse-on-unchanged-source is NOT implemented.

---

## Addressable-in-Simple Bottlenecks

All Rust-layer bottlenecks are off-limits; pure-Simple (.spl) work only:

| # | Bottleneck | Where (Simple) | Impact | Status |
|---|-----------|----------------|--------|--------|
| 1 | **Expression cascade → discriminant router** | `interpreter_eval.rs` `route_expr` | 5–10% all workloads | IMPLEMENTING (Rust — NOT addressable in .spl directly; the pure-Simple equivalent is MIR optimization patterns in `optimization_passes.spl`) |
| 2 | **Value::Str(String) → Arc<str>** | `value.rs:853` + 780 callsites | 15–25% string-heavy | DEFERRED (Rust seed — pure-Simple: minimize string copies in `src/lib/nogc_sync_mut/src/collections/` and text-handling APIs) |
| 3 | **MIR bulk ops recognizers** | `src/compiler/60.mir_opt/optimization_passes.spl` | memcpy/memset elision across all modes | Phase 1 done, 2-8 OPEN — FULLY pure-Simple |
| 4 | **SMF content-hash cache** | `src/os/smf/dynsmf_session.spl`, `src/app/startup/dynsmf_autoload.spl` | Eliminate re-parse on unchanged script | MISSING — pure-Simple implement: content-hash check before queue |
| 5 | **rt_* reduction in app-facing stdlib** | `src/lib/nogc_sync_mut/` (7974 rt_ lines), `nogc_async_mut/` (2249) | AC-9 compliance baseline | No sweep done; baseline = 7974+2249 direct rt_ calls in default lib tier |

**Fully pure-Simple targets (priority order for AC-6):**
1. MIR bulk-ops recognizer passes (general-mir-bulk-ops phases 2-8)
2. SMF content-hash cache in dynsmf_session.spl (AC-7 gap)
3. rt_* wrapping sweep in nogc_sync_mut stdlib (AC-9 baseline + reduction)
4. String copy minimization in stdlib collections (Value::Str partial mitigation)
5. Profile-guided JIT bridge integration (compiler_perf_codegen AC-2 — landed, verify effect)

---

## Script-vs-Compiler Benchmarking

Three execution modes (AC-4 requires separate tracking):

| Mode | Invocation | Characteristic |
|------|-----------|----------------|
| **Interpreter (script)** | `bin/simple file.spl` | Fast start, slow run, dev cycle |
| **SMF loader (compiler)** | `bin/simple compile → load .smf` | ~2-5x dispatch overhead |
| **Native AOT (compiler)** | `bin/simple compile --native → ./binary` | C-level throughput, slow compile step |

Cross-lang harness (`check-cross-language-perf.shs`) runs all three modes and compares to bun/python/go/erlang/java/C. Warm throughput uses in-process loops (JIT steady-state). Currently no per-mode tagging in sspec system tests (AC-3/AC-4 gap — arch tag + mode tag needed). The existing `test/05_perf/` specs are ad-hoc; no arch-tagged sspec emit benchmark docs yet.

---

## rt_* Measurement

Baseline counts (grep `rt_` in `src/lib/` excluding comments):

| Tier | rt_* lines | Default? |
|------|-----------|----------|
| `nogc_sync_mut` | 7,974 | YES (default tier) |
| `nogc_async_mut` | 2,249 | default |
| `gc_async_mut` | 1,880 | optional |
| `common` | 554 | shared |
| `nogc_async_mut_noalloc` | 358 | baremetal |

Total app-facing default-tier exposure: ~10,223 lines. Measurement command:
```bash
grep -r 'rt_' src/lib/nogc_sync_mut --include='*.spl' | grep -v '^\s*//' | wc -l
```
Goal: wrap rt_* behind stdlib public APIs in `nogc_sync_mut`; app-dev code should `use std.X`, not call `rt_*` directly.

---

## Constraints

- **Pure-Simple first** — no Rust seed / C runtime edits; `src/compiler_rust/` is off-limits
- **No API/arch break** (AC-8) — public symbol diff required after each optimization
- **E0410 export rules** — plain `use X.*` re-exports nothing; use explicit `export Name` statements
- **Default lib tier** = `nogc_async_mut` (and `nogc_sync_mut` for sync work)
- **No branches** — all work on main via jj
- **interpreter-perf-gaps Waves 11-15** are Rust-seed changes (CLOSED) — cannot replicate in .spl; only MIR/compiler layer is .spl-addressable
- **Value::Str Arc<str>** — 780 Rust callsites; deferred post-bytecode; in .spl only indirect mitigation possible

---

## Risks / Unknowns

1. **Biggest risk:** `general-mir-bulk-ops` phases 2-8 are fully open — the most impactful pure-Simple compiler optimization has zero implementation. If bulk-copy/fill/cmp recognizers conflict with existing passes or cause false-positive lowering, all compiler modes regress simultaneously.
2. SMF content-hash check requires a stable hash extern (`rt_file_read_bytes` exists; `rt_sha256` or similar may not) — needs extern audit before implementing AC-7.
3. No arch-tagged sspec benchmark harness exists yet — AC-3 is a build-from-scratch task; existing `test/05_perf/` specs are not sspec system tests and do not emit benchmark docs.
4. `compiler_perf_codegen` is implement-done but not yet verify/ship — profile-guided bridge effect is unmeasured.
5. rt_* baseline of 10,223 lines in default tiers makes AC-9 scope large; need to distinguish "app-developer callsites" from internal stdlib-to-stdlib calls before setting a reduction target.
