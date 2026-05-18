# SStack State: rust-to-simple-runtime

## User Request
> find all rust runtime or code on pure simple, 1. check make it pure simple and compare perf with rust impl 2. optimize plugin in for jit and compiler. 3. can not reach eq or better perf than go with c than add as perf bug. until all rust runtime removed. while can leave it is interface rust lib unless that make it all pure simple. with sonnet agents with opus advisor

## Task Type
refactor

## Refined Goal
> Systematically convert all C runtime modules (`src/runtime/*.c`) to pure Simple implementations, benchmark each against the C original, optimize the Simple compiler/JIT for hot paths, and file perf bugs for any module where Simple cannot reach Go/C-level performance. Interface Rust libs (hosted/*.rs platform bindings) and the seed compiler (`compiler_rust/`) are excluded. The Rust allocator bridge (`runtime_memtrack_rust.rs`) stays as it hooks `#[global_allocator]`.

## Acceptance Criteria
- [x] AC-1: Inventory — complete list of all C runtime modules with LOC, categorized as "convertible" vs "must-stay-native" with rationale
- [~] AC-2: Wave-1 conversions — ctype(9/9), error(4/4), contracts(8/8), math(13/13) DONE; hash EXISTS; base64 NEEDS REWRITE; equality/value/config DEFERRED
- [~] AC-3: Wave-2 conversions — random(21/21), time_utils(53/53), audio_effects(7/7) DONE; format/string_index/env DEFERRED
- [~] AC-4: Perf benchmarks — ctype benchmarked (0.07-0.46x C native, see §7-verify); other modules pending
- [~] AC-5: Compiler/JIT optimization — 2 optimizations identified: (1) function inlining (primary gap), (2) cross-module ABI fix; not yet implemented
- [x] AC-6: Perf bugs filed — `pure_simple_ctype_perf_gap_2026-05-18.md`, `native_cross_module_call_abi_broken_2026-05-18.md`
- [x] AC-7: "Must-stay-native" documented — see `c_runtime_exclusion_analysis_2026-05-18.md`; math/random/contracts/error/time need Rust shim rewrite; runtime.c/native/thread/simd/process/fork/sdl2/font/image stay native (GC, SIMD intrinsics, platform APIs)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-research (Analyst) — 2026-05-18
- [x] 3-arch (Architect) — 2026-05-18
- [x] 4-spec (QA Lead) — 2026-05-18
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18 (partial: ctype slice shipped, math/random/time benchmarks deferred)

## Phase Outputs

### 1-dev
**Task type:** refactor
**Scope:** Convert C runtime to pure Simple, benchmark, optimize compiler, file perf bugs.

**Inventory (34 C runtime files, 11,206 LOC total):**

| Category | Files | LOC | Notes |
|----------|-------|-----|-------|
| **Easy (convertible)** | base64, math, hash, equality, ctype, value, contracts, error, config | ~429 | Pure logic, no syscalls |
| **Medium (convertible)** | format, string_index, random, time, env, regex_stub | ~1,041 | Some SFFI for syscalls |
| **Hard (must-stay-native)** | runtime.c, native, thread, simd_*, process, fork, async_driver, sdl2, audio/effects, font, image, memtrack, wasm_shim | ~9,736 | Core GC, SIMD intrinsics, platform APIs, threading |

**Rust runtime (non-seed):**
- `runtime_memtrack_rust.rs` (80 LOC) — stays (hooks `#[global_allocator]`)
- `hosted/*.rs` (~2,420 LOC) — stays (interface libs: Cocoa, Win32, WebGPU, JS)

**Approach:** Wave-based conversion starting with easiest modules. Each wave: implement in Simple → test → benchmark → optimize → next wave.

### 2-research
**Research docs:** `research_wave1.md`, `research_wave2.md`, `research_native.md`, `research_compiler_opts.md`

**Revised conversion plan (pilot-first):**

| Priority | Module | LOC | Difficulty | Status |
|----------|--------|-----|-----------|--------|
| **Pilot** | ctype | 10 | trivial | DO FIRST — validate pipeline |
| Wave-1a | hash | 13 | trivial | Already has Simple equivalent |
| Wave-1b | base64 | 80 | trivial | Already has Simple lib |
| Wave-1c | error | 25 | easy | Needs RT_ERROR bit-pattern |
| Wave-1d | contracts | 63 | easy | Needs abort() extern |
| Wave-1e | math | 50 | easy | Transcendentals stay as libm extern |
| Wave-2a | time | 175 | medium | Pure arithmetic civil-date, highest priority |
| Wave-2b | random | 113 | medium-low | LCG math, needs atomic SFFI |
| Wave-2c | audio_effects | 87 | trivial | All stubs returning 0 |
| **Deferred** | config | 21 | needs atomics | |
| **Deferred** | value | 41 | hot path | Needs bit-cast + inlining guarantees |
| **Deferred** | equality | 126 | hot path | Needs memcmp + verified inlining |
| **Deferred** | format | 292 | high | Needs snprintf for float-to-string |
| **Deferred** | string_index | 261 | very high | No current callers |
| **Deferred** | env | 152 | mixed | Native syscall deps |
| **Skip** | regex_stub | 48 | n/a | Wire existing regex_nfa.spl instead |

**Symbol naming validated:** Simple `extern fn rt_xxx(...)` uses function name as C symbol. Replacements export identical names.

**Active perf work:** `doc/08_tracking/bug/pure_simple_collection_perf_parity_gap_2026-05-14.md` tracks ongoing perf parity (0.21x-0.89x C). AC-5 should complement, not duplicate.

**Top 5 compiler optimizations (from research):**
1. `rt_string_eq` length-mismatch short-circuit at MIR
2. Tagged-value unboxing for typed array indexing
3. XXHash64 typed-buffer path verification
4. Induction-variable bounds-check elimination
5. MIR LICM pass (listed but unimplemented)

### 3-arch
**Architecture: Pilot-first, then wave-based conversion**

**Pilot module: ctype (10 LOC C → ~30 LOC Simple)**
- Create `src/lib/common/ctype.spl` — 7 pure Simple ASCII classifiers using range checks
- `runtime_ctype.c` stays as interpreter-runtime-internal (Rust FFI, not Simple-callable)
- No symbol name conflict — Simple functions use Simple names, C uses `__is_*` prefix
- Test in interpreter mode (per memory: compile-mode has false-greens)
- Benchmark via microbenchmark harness

**Conversion pattern (applies to all waves):**
1. Create `src/lib/common/<module>.spl` or `src/lib/nogc_sync_mut/src/<module>.spl`
2. Pure Simple implementation — no `extern fn` unless truly needed (syscalls, libm)
3. Test spec at `test/unit/lib/common/<module>_spec.spl`
4. Microbenchmark at `test/perf/<module>/bench_<module>.spl`
5. For native builds: exclude the C file from `tools.rs` list if all callers migrated
6. For interpreter: C stays if Rust runtime uses it internally

**Build integration:**
- C files listed in `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`
- Each converted module can be excluded from the C list once Simple callers are migrated
- `--runtime-bundle core-c-bootstrap` controls which C files are linked

### 4-spec
Specs created and passing for all implemented modules:
- `test/unit/lib/common/ctype_spec.spl` — 9/9 PASS
- `test/unit/lib/common/audio_effects/audio_effects_spec.spl` — 7/7 PASS
- `test/unit/lib/common/random_pure_spec.spl` — 21/21 PASS
- `test/unit/lib/common/time_utils/time_utils_spec.spl` — 53/53 PASS
- Benchmark harness: `test/perf/ctype/` (bench_ctype.spl + bench_ctype_ref.c + runner)

### 5-implement
**Completed modules:**

| Module | File | LOC | Tests | Status |
|--------|------|-----|-------|--------|
| ctype (pilot) | `src/lib/common/ctype.spl` | 37 | 9/9 | DONE |
| audio_effects | `src/lib/common/audio_effects.spl` | ~30 | 7/7 | DONE |
| random_pure | `src/lib/common/random_pure.spl` | ~80 | 21/21 | DONE |
| time_utils | `src/lib/common/time_utils.spl` | ~150 | 53/53 | DONE |
| hash | Already in `hash.spl` | — | — | EXISTS (needs thin bridge) |
| base64 | `.smf` only, no `.spl` source | — | — | NEEDS REWRITE |

**Wave-1c-e (completed earlier this session):** error (4/4), contracts (8/8), math (13/13)

**Analysis docs:** `wave1a_hash_analysis.md`, `wave1b_base64_analysis.md`

### 6-refactor
**C file exclusion (ctype):**
- Deleted `src/runtime/runtime_ctype.c` — zero callers (dead code)
- Deleted `src/compiler_rust/runtime/src/value/sffi/ctype_shims.rs` — zero public functions, zero callers
- Removed from `sffi/mod.rs` (pub mod + pub use)
- Removed from `tools.rs` C file list
- Rust build verified clean (`cargo check` passes)

### 7-verify
**Benchmark results (ctype, AC-4):**

| Function | C -O2 (ops/ms) | Simple native (ops/ms) | Ratio |
|----------|----------------|----------------------|-------|
| is_digit | 1,003,071 | 464,964 | 0.46x |
| is_upper | 941,314 | 328,729 | 0.35x |
| is_lower | 603,466 | 253,957 | 0.42x |
| is_alpha | 856,594 | 125,779 | 0.15x |
| is_alnum | 1,082,562 | 77,612 | 0.07x |
| is_xdigit | 549,007 | 153,279 | 0.28x |
| is_space | 1,335,294 | 195,241 | 0.15x |
| to_lower | 1,218,049 | 236,592 | 0.19x |
| to_upper | 1,427,472 | 227,271 | 0.16x |

**Root cause:** Cranelift does not inline function calls. Leaf functions reach 0.35-0.46x C; composite functions drop to 0.07-0.15x.

**Bugs filed:**
- `native_cross_module_call_abi_broken_2026-05-18.md` — cross-module calls return wrong values
- `pure_simple_ctype_perf_gap_2026-05-18.md` — 0.07-0.46x C, inlining needed (AC-5 candidate)

### 8-ship
**Shipped (partial — ctype slice):** 2026-05-18

**Committed & pushed:**
- Deleted `runtime_ctype.c` + `ctype_shims.rs` (zero callers)
- Deleted `runtime_audio_effects.c` (zero callers, not in tools.rs)
- Removed ctype from `tools.rs` C file list and `sffi/mod.rs`
- 7 pure Simple stdlib modules: ctype(9/9), math(13/13), error(4/4), contracts(8/8), random(21/21), time_utils(53/53), audio_effects(7/7)
- Native benchmark: `bench_ctype_inline.spl` — 0.07-0.46x C (inlining gap)
- Bug reports: cross-module ABI, ctype perf gap, C exclusion analysis

**Deferred:**
- Native benchmarks for math/random/time (blocked by cross-module ABI bug for real callers)
- AC-5 compiler inlining optimization
- Wave-2+ module conversions (format, string_index, env)
- C file exclusion for math/random/contracts/error/time (active Rust/codegen callers)
