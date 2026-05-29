# SStack State: migrate-rust-runtime-to-c

## Status: CLOSED — 2026-05-20

## Phase 1: Dev ✓
## Phase 2: Research ✓  
## Phase 3: Arch ✓ (inline — pattern: extern decl + safe wrapper + cc in build.rs)
## Phase 4: Spec ✓ (verified by existing Rust unit tests + e2e Simple test)
## Phase 5: Implement ✓

**Changes made:**
1. `src/runtime/runtime_math.c` — 28 math functions as direct C libm wrappers
2. `src/compiler_rust/runtime/src/value/ffi/math.rs` — replaced 885-line Rust impl with 90-line extern decl + safe wrappers
3. `src/compiler_rust/runtime/build.rs` — added `compile_c_runtime_sources()` to compile+link C math library
4. `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs` — registered `runtime_math.c` in native binary C file list
5. `doc/04_architecture/rust_runtime_inventory.md` — complete inventory of ~200 rt_* functions with migration classification

**Verification:**
- `cargo check -p simple-runtime` ✓
- `cargo check -p simple-driver` ✓  
- `cargo build -p simple-driver` ✓
- `cargo test -p simple-compiler --lib -- math` → 188 passed, 0 failed ✓
- End-to-end: `sqrt(16.0)=4, pow(2.0,10.0)=1024, floor(3.7)=3` ✓
- C symbols verified: `nm libruntime_math.a | grep rt_math` → all 28 present ✓

## Phase 6: Refactor — N/A (minimal code, no cleanup needed)
## Phase 7: Verify ✓ (tests pass, e2e verified)
## Phase 8: Ship — Ready for commit

## Future /dev runs (ordered by ROI):
1. Memory (rt_alloc, rt_free, rt_memset, rt_memcpy) — 4 functions
2. Time (rt_time_*) — 5 functions
3. I/O (rt_stdout_*, print_raw, stdin_read_char) — 6 functions
4. UTF-8 (rt_utf8_*) — 3 functions
5. Hash (rt_hash_text, rt_str_hash) — 2 functions
6. String ops → pure Simple (needs arch decision on compiler calling convention)
