# Research: Memory Inspection and Verification Tooling for Simple

**Date:** 2026-06-11
**Purpose:** Survey the current state of Simple's memory model enforcement, compare prior-art overhead figures, and recommend a concrete three-tier tooling strategy.
**Scope:** gc/nogc compile-time enforcement, debug/test allocator instrumentation, production sampling; overhead budget; prerequisite language decisions.

---

## Table of Contents

1. [Current State of Simple's Memory Model Enforcement](#1-current-state)
2. [Prior-Art Overhead Table](#2-overhead-table)
3. [On/Off-Toggle Mechanism Analysis](#3-toggle-mechanisms)
4. [Recommendation: Three-Tier Strategy for Simple](#4-recommendation)
5. [Estimated Always-On Overhead per Tier](#5-overhead-per-tier)
6. [Gaps and Risks](#6-gaps-and-risks)

---

## 1. Current State of Simple's Memory Model Enforcement

### 1.1 Empirical Verdict

**There is no garbage collector in compiled Simple programs.** Both `gc_*` and `nogc_*`
library trees lower to identical runtime calls backed by plain libc `malloc`/`calloc`
(via Rust's global allocator). The compiler never emits a `free` or a collect cycle.
"GC mode" today mechanically means *allocate-and-leak*. Binaries produced from `gc_*`
and `nogc_*` source are byte-identical at the allocator level (see §1.2 for evidence).

The gc/nogc split therefore has **zero codegen or runtime effect**. Enforcement is
a shallow, path-literal lint that fires only when `bin/simple lint` is invoked, not
during compile or run.

### 1.2 Evidence Pointers

| Evidence | Location |
|---|---|
| `GcAlloc` → Cranelift: plain `rt_alloc` (= calloc) | `compiler/src/codegen/instr/memory.rs:163-175`, `codegen/cranelift_emitter.rs:143-144` |
| `GcAlloc` → LLVM: `build_alloca` stack slot named `"gc_alloc"` | `codegen/llvm/functions/memory.rs:78-88` |
| No `Free`/`Drop` MIR lowering exists | `grep MirInst::Free\|emit_free mir/lower` = empty |
| `rt_free`/`rt_unique_free`/`rt_shared_release` registered but never called | `codegen/runtime_sffi.rs:442-473` |
| `mir/effects.rs` models `GcAlloc` effect, feeds classification only | `mir/effects.rs:109-239` |
| gc_safety_spec: every `it` body is `pass` with assertions in comments | `test/01_unit/compiler/semantics/gc_safety_spec.spl` |
| alloc_checker_spec: entire suite commented out | `test/01_unit/compiler/semantics/alloc_checker_spec.spl` |

### 1.3 Existing Enforcement Infrastructure

**Compiler-side (self-hosted only — not in deployed `bin/simple`):**

- `src/compiler/00.common/gc_config.spl` — `GcMode(Gc|NoGc)`, hierarchy: project default → `__init__.spl @no_gc` → file `@no_gc`.
- `noalloc_checker` — hard errors on allocation inside `@noalloc` functions; transitive call analysis. Lives in self-hosted compiler; spec skipped.
- `gc_boundary_check` — import-direction rules over `RUNTIME_FAMILY_MANIFEST` rank table (`nogc` must not import `gc`; `noalloc` must not import any allocating family). Deployed as `bin/simple lint` warning/deny. Does **not** run at compile or test time.

**Runtime-side (deployed):**

- `src/runtime/runtime_memtrack.h` — `SPL_MALLOC/CALLOC/REALLOC/STRDUP` tagged wrappers; `g_memtrack_enabled` hash-table tracking; `spl_memtrack_snapshot/dump_since/count_since/bytes_since`; alloc listener hook. Enabled via `SIMPLE_MEMTRACK=1`.
- `src/lib/nogc_sync_mut/mem_tracker/` — Simple wrapper: `mem_enable/snapshot/phase/diff/group_by_tag/report`, `parse_leak_dump`.
- `src/lib/nogc_sync_mut/sanitizer/lsan/` — `lsan_enable/checkpoint/check_since/suppress_tag/report`; built on memtrack (not LLVM LSan).
- `src/runtime/runtime.c:1012-1014` — `spl_malloc` → `mi_malloc` when mimalloc present, else system malloc. Production runtime has `spl_free_value/spl_array_free/spl_dict_free` eager recursive free.
- `src/lib/allocator.spl` — pluggable allocator scaffold (System/Arena/Pool/Slab); extern bindings commented out — design scaffold only.
- Aspiration: `doc/05_design/runtime/gc_pure_simple_implementation.md` — mark-sweep GC in Simple (`src/app/gc/core.spl`), opt-in, not default; Rust `gc.rs` marked UNUSED.

**Lint blind spots:**

- `gc_boundary_crossing` (Deny) fires only on literal `std.<family>.…` import segments, only when `lint` is explicitly run.
- Compile and test runs bypass boundary checks entirely.
- Interpreter mode: `it` bodies do not execute in the deployed interpreter, so specs that test enforcement logic are effectively silent.

---

## 2. Prior-Art Overhead Table

Sources: cited URLs retained for traceability.

| Tool / Technique | CPU overhead (on) | Memory overhead (on) | When-off cost | Source |
|---|---|---|---|---|
| AddressSanitizer (ASan) | ~2x avg (up to 5x edge cases) | ~2–4x | Zero — separate compile | [Clang ASan docs](https://clang.llvm.org/docs/AddressSanitizer.html), [Serebryany et al. 2012](https://www.academia.edu/83062177/AddressSanitizer_A_Fast_Address_Sanity_Checker) |
| LeakSanitizer (LSan, standalone) | Near zero (exit-phase check only) | Small per-alloc bookkeeping | Zero — separate link flag | [Clang LSan docs](https://clang.llvm.org/docs/LeakSanitizer.html) |
| MemorySanitizer (MSan) | ~3x avg | ~2x avg | Zero — separate compile; whole-program required | [Clang MSan docs](https://clang.llvm.org/docs/MemorySanitizer.html) |
| ThreadSanitizer (TSan) | ~5–15x | ~5–10x | Zero — separate compile | [Clang TSan docs](https://clang.llvm.org/docs/ThreadSanitizer.html) |
| UBSan | ≤40% per sub-check; ~228% all-on | Minimal | Zero — separate compile | [Clang UBSan docs](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html) |
| HWASan | Lower than ASan (Android whole-system) | Much smaller than ASan | Zero — needs AArch64 TBI | [Clang HWASan design](https://clang.llvm.org/docs/HardwareAssistedAddressSanitizerDesign.html) |
| ARM MTE | Up to 2.37x worst-case (SYNC); ASYNC designed always-on | 4-bit tag per 16-byte granule | Zero when not enabled | [arXiv 2601.11786](https://arxiv.org/html/2601.11786v1) |
| GWP-ASan (sampled guard pages) | Near-zero — deployed fleet-wide Chrome/Android | Negligible fixed guard-page pool | ~0% (one sampled branch/alloc); zero if compiled out | [arXiv:2311.09394](https://arxiv.org/abs/2311.09394), [Chromium GWP-ASan](https://www.chromium.org/Home/chromium-security/articles/gwp-asan/) |
| Valgrind memcheck | 20–30x | ~2x + ~120 B/alloc | Zero — external tool | [Valgrind manual](https://valgrind.org/docs/manual/valgrind_manual.pdf) |
| Miri (Rust interpreter UB) | 10–100x | Interpreter heap model | Zero — dev tool only | [Miri PACMPL paper](https://dl.acm.org/doi/10.1145/3776690) |
| mimalloc MI_DEBUG_FULL | Moderate — per-alloc metadata + pattern fill | Padding + metadata | Zero — separate cmake build type | [mimalloc modes](https://microsoft.github.io/mimalloc/modes.html) |
| mimalloc MI_GUARDED | ~0–1% (sample-rate-dependent) | Small guard-page pool | ~0% (one branch/alloc when compiled in; zero if build excludes `-DMI_GUARDED`) | [mimalloc readme](https://github.com/microsoft/mimalloc/blob/main/readme.md) |
| mimalloc MI_SECURE | ~10% | Small | ~0% (one branch/alloc) | [mimalloc modes](https://microsoft.github.io/mimalloc/modes.html) |
| Zig DebugAllocator / Odin Tracking_Allocator | Per-alloc metadata + stack trace | Per-alloc records | Zero — release passes different allocator value | [zig.guide allocators](https://zig.guide/standard-library/allocators/) |
| heaptrack (alloc profiler) | Low — only on alloc path; DWARF deferred | Trace buffer | Zero — LD_PRELOAD only when profiling | [KDE/heaptrack](https://github.com/KDE/heaptrack) |
| bytehound (alloc profiler) | High — full stack trace every alloc, no sampling | High (full per-alloc records) | Zero — LD_PRELOAD only | [koute/bytehound](https://github.com/koute/bytehound) |
| tcmalloc/jemalloc sampled profiling | ~1% at 512 KB interval; ~20x full non-sampled | Sampled-stack table | Zero — LD_PRELOAD / build flag | [PingCAP heap deep dive](https://dzone.com/articles/troubleshooting-memory-leaks-deep-dive-into-common-heap-profilers) |
| D `@nogc` compile-time enforcement | 0 (compile-time only) | 0 | 0 always | [dlang.org/spec/garbage.html](https://dlang.org/spec/garbage.html) |

---

## 3. On/Off-Toggle Mechanism Analysis

Ranked by when-off cost (best to worst):

1. **Compile-time enforcement** (D `@nogc`, Rust borrow checker) — Zero runtime cost on *or* off. The check lives in the compiler; nothing enters the binary. This is the only category that costs zero even when active.

2. **Compile-time elision / build flavor** (clang sanitizers, Go `-race`, mimalloc `MI_DEBUG_FULL`) — Not in release binary; truly zero when off. Trade-off: binary proliferation; bugs may only surface in the instrumented flavor.

3. **Allocator-value / vtable swap at startup** (Zig allocator parameter, Odin `context.allocator`) — One indirect call per allocation either way. Swapping a tracking allocator in costs nothing *extra* beyond the indirection that already exists. Near-zero when off.

4. **Link-time interposition** (weak symbols, `LD_PRELOAD`, heaptrack) — Zero when no interposer is loaded. Allows post-hoc tooling without rebuild.

5. **Sampling behind a runtime flag** (GWP-ASan, mimalloc `MI_GUARDED`, tcmalloc sampled profiling) — Code ships in production binary; "off" cost is one predictable branch per allocation. Negligible, not literally zero. Chrome/Android run GWP-ASan fleet-wide on this model ([arXiv:2311.09394](https://arxiv.org/abs/2311.09394)).

6. **External binary-translation tools** (Valgrind, Miri) — Zero in production by definition; 20–100x when active. CI/dev only.

**Key insight for Simple:** The `nogc_*` / `gc_*` directory hierarchy already encodes the D `@nogc` contract structurally. Tier 1 work is formalizing what the tree layout already promises, at zero runtime cost. Tiers 2 and 3 layer debug and production instrumentation on top via mechanisms already present in the deployed mimalloc runtime.

---

## 4. Recommendation: Three-Tier Strategy for Simple

### Tier 1 — Compile-Time Enforcement (zero runtime cost)

**Extend `noalloc_checker`/`gc_boundary_check` to transitive D-style `@nogc` enforcement.**

- Promote `gc_boundary_check` from lint-only to a compile-time error (or mandatory pre-test gate).
- Enable `noalloc_checker` in the deployed compiler path (it exists in self-hosted but is not deployed).
- Add transitive effect inference: if a function calls a function that allocates, propagate the violation up the call chain — matching D's template inference model ([dlang.org/spec/garbage.html](https://dlang.org/spec/garbage.html)).
- Wire the `alloc_checker` spec suite (currently commented out) and make it green before shipping.
- Cost: **zero runtime cost on or off**. Compile time may increase slightly for deep call graphs.
- Leverage: turns the existing directory convention into a compiler-verified guarantee, catching import-direction violations at compile time not just at `bin/simple lint`.

### Tier 2 — Test/Debug Build Flavor (overhead in debug only)

**`--debug-alloc` build flavor using mimalloc `MI_DEBUG_FULL` + existing `memtrack`/`lsan` wrappers.**

- Introduce a `bin/simple build --debug-alloc` flavor (cmake `MI_DEBUG=3` / `MI_DEBUG_FULL`). The `bin/simple test` runner uses this flavor by default, analogous to Zig's `std.testing.allocator`.
- The existing `runtime_memtrack.h` tagged wrappers and `mem_tracker`/`lsan` Simple library wrap the mimalloc debug mode; expand the test fixture corpus beyond the current three fixtures (`no_leak`, `array_alloc`, `string_alloc`) to include struct, dict, and cross-module cases.
- Add ASan+LSan as a CI-only flavor of the C runtime (`-fsanitize=address,leak`); applies directly to `rt_*` externs at zero release cost.
- Cost when on: per-alloc metadata + invariant checks (moderate); **literal zero when off** — the release build never links the debug allocator.

### Tier 3 — Production Sampling (negligible always-on cost)

**`mimalloc MI_GUARDED` for GWP-ASan-style heap-buffer-overflow/UAF detection in release binaries.**

- Compile release binaries with `-DMI_GUARDED`; tune `MIMALLOC_GUARDED_SAMPLE_RATE` (default 1/4000 per mimalloc) via env var, identical to Chrome/Android GWP-ASan deployment ([arXiv:2311.09394](https://arxiv.org/abs/2311.09394)).
- No new dependency: Simple already ships mimalloc.
- Cost: one predictable sampled branch per allocation (~0–1% CPU, negligible memory for the guard-page pool). Builds without `-DMI_GUARDED` are zero cost.

**Supplementary (CI only, no language work):** Valgrind memcheck spot-checks (20–30x, scheduled on representative workloads only); interpreter-mode provenance checks as Simple's Miri analogue (10–100x acceptable because the interpreter is already the slow path).

**Avoid as default gates:** TSan (5–15x), MSan (3x, whole-program constraint), bytehound-style full-trace profiling in anything long-running.

---

## 5. Estimated Always-On Overhead per Tier

| Tier | Mechanism | CPU overhead when on | Memory overhead when on | When-off cost |
|---|---|---|---|---|
| 1 — Compile-time enforcement | Transitive `@nogc` effect in compiler | 0 (compile-time only) | 0 | 0 |
| 2 — Debug/test flavor | mimalloc `MI_DEBUG_FULL` + memtrack/lsan | Moderate (per-alloc fill + checks) | Padding + call-site metadata | 0 — separate build |
| 2 — CI ASan+LSan | Clang `-fsanitize=address,leak` on runtime | ~2x CPU, ~2–4x memory | Shadow map ~1/8 address space | 0 — separate build |
| 3 — Production sampling | mimalloc `MI_GUARDED` (1/4000 default) | ~0–1% | Small guard-page pool | ~0% (one branch/alloc); 0 if compiled out |

---

## 6. Gaps and Risks

1. **"GC" currently means allocate-and-leak — a language decision is prerequisite.**
   Before Tier 1 enforcement is meaningful, the project must decide: will `gc_*` trees
   eventually get a real garbage collector, use eager-free (like `spl_free_value` already
   does), use reference counting, or remain intentionally leak-based (arena/epoch)?
   The aspirational mark-sweep (`src/app/gc/core.spl`, `doc/05_design/runtime/gc_pure_simple_implementation.md`)
   is not deployed. Until this decision is made, "nogc avoids GC" is vacuously true, and
   compile-time enforcement of that boundary enforces a contract with no counterpart.

2. **`noalloc_checker` and `alloc_checker` are in the self-hosted compiler, not deployed.**
   `bin/simple` is the Rust seed. Any Tier 1 improvement requires porting or enabling
   these passes in `src/compiler_rust/` or deploying the self-hosted compiler.

3. **`gc_boundary_check` is lint-only.**
   It does not run at compile or test time. A CI step that runs `bin/simple lint` on the
   full source tree as a required gate would close this gap immediately with no compiler
   work.

4. **Test fixture corpus is tiny.**
   `test/fixtures/leak_check/` has three fixtures; struct, dict, closure, and
   cross-module cases are absent. Debug-flavor tests (Tier 2) need a broader corpus to
   have detection value.

5. **`src/lib/allocator.spl` is a design scaffold, not production.**
   The pluggable allocator abstraction (System/Arena/Pool/Slab) has extern bindings
   commented out. Completing it would enable Zig-style allocator-value swapping (Tier 2
   mechanism 3 from §3), giving test code a different allocator without recompiling the
   runtime.

6. **Interpreter-mode enforcement gap.**
   `it` bodies in the deployed interpreter do not execute, making spec-based enforcement
   tests silent false greens. Interpreter-mode provenance checking (Simple's Miri
   analogue) requires a separate runtime hook, not just spec additions.
