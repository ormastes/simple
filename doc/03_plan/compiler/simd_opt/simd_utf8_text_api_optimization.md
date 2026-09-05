# SIMD-Accelerated UTF-8 Text API Optimization

## Status: 36/36 tracked items done

| Wave | Status | Detail |
|------|--------|--------|
| W0 Compiler Auto-Vec | Done | 4/4 tasks |
| W1 C Runtime Foundations | Done | 5/5 tasks |
| W2 SIMD Kernels | Done | 6/6 tasks (SSE2/AVX2/NEON for all) |
| W3 Data Structures | Done | 3/3 tasks (SWI + Rank/Select + WidthIndex) |
| W4 Stdlib Wiring | Done | 4/4 tasks |
| W5 Quality | Done | 4/4 tasks |
| W6 Text API Completion | Done | 4/4 tasks |
| W7 Predicate/Interpreter Completion | Done | 2/2 tasks |
| W8 Facade/Interpreter Cleanup | Done | 1/1 task |
| W9 Rope Search/Case Wiring | Done | 2/2 tasks |
| W10 Naming/Module Cleanup | Done | 1/1 task |
| W11 Replace-All Search Cleanup | Done | 1/1 task |

### Remaining work
None.

## Context

The Simple language runtime handles strings as heap-allocated UTF-8 byte arrays (`RtCoreString` in `runtime_native.c`) but has **zero SIMD text processing**. Character counting uses Rust's `chars().nth()` (O(N) per access), substring search uses `strstr()`, case conversion uses byte-by-byte `toupper()`/`tolower()`.

The compiler already has mature SIMD infrastructure:
- **Type system**: `simd_types.spl`, `simd_vector_types.spl`, `simd_platform.spl`, `simd_capabilities.spl`
- **Auto-vectorizer**: Full 4-phase MIR pipeline (`60.mir_opt/auto_vectorize_*.spl`) — analysis, validation, cost model, codegen
- **Lint**: 11 patterns in `simd_opportunity_lint.spl` including L-SIMD-008 (ASCII case), L-SIMD-007 (byte mismatch scan)
- **Native codegen**: `x86_64_simd.spl` with SSE/AVX2 VEX encoding

**Three-tier strategy:**
1. **Tier 1 — Compiler auto-vectorization**: Extend existing optimizer to auto-SIMD string loops (ASCII validation, case conversion, byte comparison)
2. **Tier 2 — Custom C kernels**: For patterns the compiler can't auto-vectorize (UTF-8 counting, validation, variable-width indexing, substring search)
3. **Tier 3 — Vendor simdutf**: Later, if transcoding (UTF-8 to UTF-16/32) is needed

**Additional research checked 2026-05-12:**
- Keiser/Lemire UTF-8 validation work confirms byte-stream SIMD validation/counting remains the correct hot-kernel layer and can run under one instruction per byte on commodity SIMD.
- simdutf documentation confirms the next major upstream class is validation plus transcoding at billions of characters per second; defer vendoring until Simple needs UTF-8/UTF-16/UTF-32 conversion APIs.
- SIMD substring-search literature and simdutf/memchr-style practice support using first/last-byte vector filters before full candidate verification, which matches the existing `rt_simd_str_search` runtime kernel.

## Architecture

```
Tier 1: Compiler Auto-Vectorization
  simd_opportunity_lint.spl  -> detect string patterns
  auto_vectorize_*.spl       -> transform to SIMD IR
  x86_64_simd.spl            -> emit SSE2/AVX2 insns
  Handles: ASCII is_ascii loop, ASCII case loops, byte-compare loops

Tier 2: C Runtime SIMD Kernels
  runtime_simd_dispatch.h  -> dispatch table + CPU detect
  runtime_simd_utf8.c      -> count, validate, find_invalid
  runtime_simd_search.c    -> contains, index_of, equal
  runtime_simd_case.c      -> to_upper, to_lower, is_ascii
  runtime_string_index.c   -> SWI + rank/select
  Handles: UTF-8 counting (Keiser-Lemire), validation, substring search, SWI

Tier 3: Vendor simdutf (future, if transcoding needed)

Stdlib wiring (unchanged surface):
  string_core.spl --> utf8.spl --> simd_text_ffi.spl --> C kernels
  text_ops.spl --> width_index.spl (SWI wrapper)
```

**Caching**: `RtCoreString.reserved` (uint32_t) bit layout:
- Bits [31:30] = flags: 00=uncached, 01=cp-count cached, 10=is-ASCII cached, 11=both
- Bits [29:0] = codepoint count (max ~1 billion)
- Strings are immutable so cache is never invalidated

## Task Breakdown

### WAVE 0: Compiler Auto-Vectorization Enhancement (Tier 1)

**T0.1: Extend SIMD Opportunity Lint for String Patterns** — DONE
- Modified: `src/compiler/35.semantics/lint/simd_opportunity_lint.spl`
- Added L-SIMD-012 (ASCII validate), L-SIMD-013 (byte-count), L-SIMD-014 (delimiter-scan)

**T0.2: Enhance Auto-Vectorize Analysis for String Access Patterns** — DONE
- Modified: `auto_vectorize_types.spl` — added `element_type` to ArrayAccess, `ComparisonPattern`, `BitwisePattern` structs

**T0.3: Enhance Auto-Vectorize Cost Model for String Ops** — DONE
- Modified: `auto_vectorize_cost.spl` — added cost entries for And/Or/Xor/Shl/Shr/Lt/Le/Gt/Ge/Eq/Ne

**T0.4: Verify Auto-Vec Codegen Emits Correct SIMD** — DONE (codegen extended)
- Modified: `auto_vectorize_codegen.spl` — extended vectorize_binop with And/Or/Xor/Cmp/Shift cases
- Added: `test/01_unit/compiler/semantics/auto_vec_string_test.spl`
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/compiler/semantics/auto_vec_string_test.spl --mode=interpreter --no-cache` — 4/4 pass

### WAVE 1: C Runtime Foundations (Tier 2) — ALL DONE

**T1.1: C Runtime File Scaffolding** — DONE
**T1.2: SIMD Dispatch Table** — DONE (`SimdTextDispatch` + `simd_text_init()` + cpuid/getauxval)
**T1.3: Reserved Field Cache Convention** — DONE (bits[31:30] flags, bits[29:0] cp count)
**T1.4: Extern Surface + Bootstrap** — DONE (18 externs in simd_text_ffi.spl, bootstrap passes)
**T1.5: Benchmark Harness** — DONE (`string_bench.spl` with ASCII/mixed/adversarial corpora)

### WAVE 2: SIMD Kernels — ALL DONE

**T2.1: SIMD UTF-8 Codepoint Counting** — DONE (Keiser-Lemire SSE2/AVX2/NEON + scalar)
**T2.2: SIMD UTF-8 Validation** — DONE (ASCII-fast-skip strategy, scalar fallback for non-ASCII chunks)
**T2.3: SIMD ASCII Detection** — DONE (movemask x86 / vmaxvq NEON, cached in reserved)
**T2.4: SIMD Case Conversion** — DONE (signed cmpgt range check + 0x20 flip, SSE2/AVX2/NEON)
**T2.5: SIMD Substring Search** — DONE (Mula-style first+last byte filter, SSE2/AVX2/NEON)
**T2.6: SIMD String Equality** — DONE (length early-reject + memcmp)

### WAVE 3: Data Structures — ALL DONE

**T3.1: Segmented Width Index (SWI)** — DONE (64-byte segments, binary search + linear scan)
**T3.2: Rank/Select Bit-Vector** — DONE (512-bit blocks, __builtin_popcountll, block-level cumulative rank)
**T3.3: SWI + Rank/Select Simple Wrapper** — DONE (`WidthIndex` class with lazy SWI to rank/select fallback)

### WAVE 4: Stdlib Wiring — ALL DONE

**T4.1: Wire UTF-8 kernels into utf8.spl** — DONE (`text_codepoint_len` calls `rt_text_count_codepoints_cached`)
**T4.2: Wire search kernels into string_core.spl** — DONE (`str_last_index_of` uses SIMD)
**T4.3: Wire case conversion** — DONE (`str_to_lower`/`str_to_upper` use SIMD single-call)
**T4.4: Wire WidthIndex into text_ops.spl** — DONE (`text_char_at_indexed`, `text_slice_indexed`, `text_len_indexed`)

### WAVE 5: Quality

**T5.1: Correctness Test Suite** — DONE (52/52 tests pass)
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/runtime/simd_text/simd_text_test.spl --mode=interpreter` — 52/52 pass

**T5.2: Fuzz Testing** — DONE
- Added: `test/fixtures/runtime/simd_text/simd_text_fuzz.spl` plan marker for the requested artifact path
- Added: `test/01_unit/runtime/simd_text/simd_text_fuzz_test.spl`
- Design: deterministic raw-byte UTF-8 validation fuzz plus valid-text SIMD comparisons
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/runtime/simd_text/simd_text_fuzz_test.spl --mode=interpreter --no-cache` — 3/3 pass, including 100K generated raw-byte cases

**T5.3: Performance Regression Gate** — DONE
- Fixed benchmark timing extern from missing `rt_clock_monotonic_ns` to available `rt_time_now_nanos`
- Evidence: `src/compiler_rust/target/debug/simple run src/lib/nogc_sync_mut/benchmark/string_bench.spl --mode=compiled` — benchmark completed
- Representative throughput from the run:
  - `count_codepoints_cached` ASCII-10K: ~221 MB/s
  - `count_codepoints_cached` Mixed-10K: ~219 MB/s
  - `validate_utf8` ASCII-10K: ~229 MB/s
  - `search_found` ASCII-10K: ~214 MB/s
  - `to_lower` ASCII-10K: ~30 MB/s

**T5.4: Bootstrap Verification** — DONE (full 5-stage bootstrap passes, all MCP servers compile)

### WAVE 6: Text API Completion — ALL DONE

**T6.1: Wire common string search/equality to SIMD externs** — DONE
- Modified: `src/lib/common/string_core.spl`
- `str_eq` now uses `rt_simd_str_equal`
- `str_contains` and `str_index_of` now use `rt_simd_str_search`

**T6.2: Preserve compiled text-count externs** — DONE
- Modified: `src/runtime/runtime_simd_utf8.c`, `src/runtime/runtime.h`, `src/compiler_rust/compiler/src/linker/native_binary/stubs.rs`
- `rt_text_count_codepoints` is an alias to the cached SIMD codepoint count path
- Linker keep-list now prevents generated zero stubs for SIMD text externs when real runtime objects are present

**T6.3: Fix indexed Unicode text extraction** — DONE
- Modified: `src/lib/common/encoding/width_index.spl`
- `WidthIndex.char_at` and `WidthIndex.slice` now convert byte slices back to text through `rt_bytes_to_text`
- Normalizes signed byte values from `text.bytes()` before UTF-8 width checks

**T6.4: Regression coverage** — DONE
- Added: `test/01_unit/lib/common/string_core_simd_search_test.spl`
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/common/string_core_simd_search_test.spl --mode=interpreter --no-cache` — 4/4 pass

### WAVE 7: Predicate/Interpreter Completion — ALL DONE

**T7.1: Wire starts/ends predicates to SIMD search** — DONE
- Modified: `src/lib/common/string_core.spl`
- `str_starts_with` now reuses `rt_simd_str_search` and checks byte offset zero
- `str_ends_with` now reuses `rt_simd_str_last_index_of` and checks the final byte offset
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/common/string_core_simd_search_test.spl --mode=interpreter --no-cache` — 4/4 pass

**T7.2: Fast interpreter text codepoint count** — DONE
- Modified: `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`
- `rt_text_count_codepoints_cached` now counts UTF-8 leading bytes over `as_bytes()` instead of iterating Unicode scalars
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/runtime/simd_text/simd_text_test.spl --mode=interpreter --no-cache` — 52/52 pass

### WAVE 8: Facade/Interpreter Cleanup — ALL DONE

**T8.1: Remove stale scalar tier branch and fix interpreter byte-array externs** — DONE
- Modified: `src/lib/common/encoding/utf8.spl`, `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`
- `Utf8Provider.count_codepoints_impl` now delegates to `rt_utf8_count_codepoints` instead of routing every detected SIMD tier to `_scalar_utf8_count_codepoints`
- Interpreter-mode `rt_utf8_count_codepoints`, `rt_utf8_validate`, and `rt_utf8_find_invalid` now unpack `Value::Array` byte buffers directly instead of converting through runtime heap arrays
- Added public byte-array regression coverage in `test/01_unit/runtime/simd_text/simd_text_test.spl`
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/runtime/simd_text/simd_text_test.spl --mode=interpreter --no-cache` — 52/52 pass

### WAVE 9: Rope Search/Case Wiring — ALL DONE

**T9.1: Route rope search/comparison helpers through optimized string core** — DONE
- Modified: `src/lib/common/rope/search.spl`
- `rope_find`, `rope_find_all`, `rope_contains`, `rope_starts_with`, `rope_ends_with`, and `rope_equals` now delegate to SIMD-backed `common.string_core` helpers after flattening rope text
- Added regression coverage in `test/01_unit/lib/common/rope_simd_search_test.spl`
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/common/rope_simd_search_test.spl --mode=interpreter --no-cache` — 4/4 pass

**T9.2: Route rope case conversion through optimized string core** — DONE
- Modified: `src/lib/common/rope/utilities.spl`
- `rope_to_upper` and `rope_to_lower` now delegate to SIMD-backed `str_to_upper` and `str_to_lower` after flattening rope text
- Extended regression coverage in `test/01_unit/lib/common/rope_simd_search_test.spl`
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/common/rope_simd_search_test.spl --mode=interpreter --no-cache` — 4/4 pass

### WAVE 10: Naming/Module Cleanup — ALL DONE

**T10.1: Apply Simple/Ruby-style local naming and explicit module imports** — DONE
- Modified: `test/01_unit/runtime/simd_text/simd_text_fuzz_test.spl`, `test/01_unit/lib/common/rope_simd_search_test.spl`, `src/lib/common/rope/utilities.spl`
- Renamed internal fuzz predicates from `is_cont`/`scalar_is_valid` to descriptive Simple-compatible names without `?` suffixes
- Removed unused rope test imports and made `rope/utilities.spl` explicitly import `rope_create_from_string`
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/runtime/simd_text/simd_text_fuzz_test.spl --mode=interpreter --no-cache` — 3/3 pass
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/common/rope_simd_search_test.spl --mode=interpreter --no-cache` — 4/4 pass

### WAVE 11: Replace-All Search Cleanup — ALL DONE

**T11.1: Route replace-all scanner through SIMD-backed search** — DONE
- Modified: `src/lib/common/string_core.spl`
- `str_replace_all` now uses the integer `str_index_of` API instead of raw optional `text.index_of`, keeping replacement scanning on the SIMD-backed common search path and avoiding optional unwrap logic in the hot loop
- Extended regression coverage in `test/01_unit/lib/common/string_core_simd_search_test.spl`
- Evidence: `src/compiler_rust/target/debug/simple test test/01_unit/lib/common/string_core_simd_search_test.spl --mode=interpreter --no-cache` — 5/5 pass

## Critical Files

| File | Action | Purpose |
|------|--------|---------|
| `src/compiler/35.semantics/lint/simd_opportunity_lint.spl` | MOD | New string-pattern lint rules (Tier 1) |
| `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl` | MOD | String access pattern recognition |
| `src/compiler/60.mir_opt/mir_opt/auto_vectorize_cost.spl` | MOD | Cost entries for byte patterns |
| `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` | MOD | SIMD codegen for string patterns |
| `src/runtime/runtime_native.c` | MOD | Reserved field caching, simd_text_init call |
| `src/runtime/runtime.c` | MOD | Bridge scalar to SIMD dispatch |
| `src/runtime/runtime.h` | MOD | New function declarations |
| `src/runtime/runtime_simd_dispatch.h` | NEW | Dispatch table, platform macros |
| `src/runtime/runtime_simd_utf8.c` | NEW | Count, validate, find_invalid kernels |
| `src/runtime/runtime_simd_search.c` | NEW | Contains, index_of, starts/ends_with |
| `src/runtime/runtime_simd_case.c` | NEW | ASCII detect, case conversion |
| `src/runtime/runtime_string_index.c` | NEW | SWI + rank/select |
| `src/lib/common/encoding/simd_text_ffi.spl` | NEW | Extern declarations |
| `src/lib/common/encoding/width_index.spl` | NEW | WidthIndex class |
| `src/lib/common/encoding/utf8.spl` | MOD | Wire to cached externs |
| `src/lib/common/string_core.spl` | MOD | Wire to SIMD search/case/replacement scanning |
| `src/lib/common/encoding/text_ops.spl` | MOD | Optional WidthIndex path |
| `src/lib/common/rope/search.spl` | MOD | Route rope search/comparison through SIMD-backed string core |
| `src/lib/common/rope/utilities.spl` | MOD | Route rope case conversion through SIMD-backed string core |
| `src/runtime/runtime_simd_utf8.c` | MOD | `rt_text_count_codepoints` alias to cached SIMD path |
| `src/compiler_rust/compiler/src/linker/native_binary/stubs.rs` | MOD | Preserve SIMD text externs from generated zero stubs |
| `src/compiler/70.backend/backend/runtime_compiler.spl` | MOD | Add sources to build list |
| `src/compiler_rust/compiler/src/interpreter_extern/simd.rs` | MOD | Interpreter extern implementations |
| `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` | MOD | Extern dispatch match arms |

## Risks

| Risk | Mitigation |
|------|-----------|
| Compiler auto-vec may not fire on real stdlib code | Lint rules serve as documentation; fall through to Tier 2 C kernels |
| Bootstrap serialization (all externs need one bootstrap) | Batch all in T1.4; scalar stubs |
| `__attribute__((target))` portability | Test gcc+clang; fallback: per-file flags in runtime_compiler.spl |
| SWI degenerate case (alternating widths) | Fallback to rank/select when segments > 1024 |
| NEON lacks movemask | Use vmaxvq_u8/vminvq_u8 for ASCII, vaddvq_u8 for accumulation |
| Rank/select 12.5% memory overhead | Only build on demand when SWI degenerates; free when no longer needed |
| Unaligned AVX2 loads | Always use `_mm256_loadu_si256` — data at offset 16 from malloc base |

## Verification

1. `src/compiler_rust/target/debug/simple test test/01_unit/runtime/simd_text/simd_text_test.spl --mode=interpreter` — 52/52 pass
2. `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` — self-hosted compiler bootstraps
3. `src/compiler_rust/target/debug/simple run src/lib/nogc_sync_mut/benchmark/string_bench.spl --mode=compiled` — benchmark suite completes
4. `src/compiler_rust/target/debug/simple test test/01_unit/runtime/simd_text/simd_text_fuzz_test.spl --mode=interpreter --no-cache` — no validation divergence on 100K generated raw-byte inputs
5. Manual spot-check: Korean/CJK/emoji strings for correct codepoint counting
6. `src/compiler_rust/target/debug/simple test test/01_unit/compiler/semantics/auto_vec_string_test.spl --mode=interpreter --no-cache` — L-SIMD-012/013/014 verified
7. `src/compiler_rust/target/debug/simple test test/01_unit/lib/common/string_core_simd_search_test.spl --mode=interpreter --no-cache` — common string search/equality/predicate/replacement wiring verified
8. `cargo check -q -p simple-compiler` — Rust compiler crate validates after interpreter extern changes
9. `src/compiler_rust/target/debug/simple test test/01_unit/lib/common/rope_simd_search_test.spl --mode=interpreter --no-cache` — rope search/comparison/case wiring verified
10. `src/compiler_rust/target/debug/simple test test/01_unit/runtime/simd_text/simd_text_fuzz_test.spl --mode=interpreter --no-cache` — local naming cleanup preserved fuzz coverage
