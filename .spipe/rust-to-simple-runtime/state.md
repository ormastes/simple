# SStack State: rust-to-simple-runtime

## User Request
> find all rust runtime or code on pure simple, 1. check make it pure simple and compare perf with rust impl 2. optimize plugin in for jit and compiler. 3. can not reach eq or better perf than go with c than add as perf bug. until all rust runtime removed. while can leave it is interface rust lib unless that make it all pure simple. with sonnet agents with opus advisor

## Task Type
refactor

## Refined Goal
> Systematically convert all C runtime modules (`src/runtime/*.c`) to pure Simple implementations, benchmark each against the C original, optimize the Simple compiler/JIT for hot paths, and file perf bugs for any module where Simple cannot reach Go/C-level performance. Interface Rust libs (hosted/*.rs platform bindings) and the seed compiler (`compiler_rust/`) are excluded. The Rust allocator bridge (`runtime_memtrack_rust.rs`) stays as it hooks `#[global_allocator]`.

## Acceptance Criteria
- [ ] AC-1: Inventory — complete list of all C runtime modules with LOC, categorized as "convertible" vs "must-stay-native" with rationale
- [ ] AC-2: Wave-1 conversions — pure Simple replacements for all "easy" modules (base64, math, hash, equality, ctype, value, contracts, error, config) with passing tests
- [ ] AC-3: Wave-2 conversions — pure Simple replacements for "medium" modules (format, string_index, random, time, env, regex_stub) with passing tests
- [ ] AC-4: Perf benchmarks — each converted module benchmarked against C original; results documented
- [ ] AC-5: Compiler/JIT optimization — at least 2 concrete compiler optimizations identified and implemented to close perf gaps
- [ ] AC-6: Perf bugs filed — any module where Simple is >2x slower than C after optimization gets a concrete perf bug filed in doc/bugs/
- [ ] AC-7: "Must-stay-native" modules (runtime.c, native, thread, simd_*, process, fork, async_driver, sdl2, audio, font, image) documented with clear rationale why they can't be pure Simple yet

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

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
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
