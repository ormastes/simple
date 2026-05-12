# SIMD-Accelerated UTF-8 Text API Optimization

## Status: 22/24 tasks done

| Wave | Status | Detail |
|------|--------|--------|
| W0 Compiler Auto-Vec | Done | 4/4 tasks |
| W1 C Runtime Foundations | Done | 5/5 tasks |
| W2 SIMD Kernels | Done | 6/6 tasks (SSE2/AVX2/NEON for all) |
| W3 Data Structures | Done | 3/3 tasks (SWI + Rank/Select + WidthIndex) |
| W4 Stdlib Wiring | Done | 4/4 tasks |
| W5 Quality | 2 remaining | T5.2 fuzz test, T5.3 perf benchmarks |

### Remaining work
1. **T5.2** — Create `test/runtime/simd_text_fuzz.spl` (random byte sequences, scalar vs SIMD comparison)
2. **T5.3** — Run `string_bench.spl` in compiled mode, verify speedup thresholds
3. **T0.4 (minor)** — Create `test/compiler/auto_vec_string_test.spl` end-to-end test

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
- REMAINING: Create `test/compiler/auto_vec_string_test.spl` end-to-end test

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

**T5.1: Correctness Test Suite** — DONE (47/47 tests pass)
- WidthIndex tests excluded from interpreter mode (`me`-receiver limitation); verified via bootstrap compiled mode

**T5.2: Fuzz Testing** — NOT DONE
- Create: `test/runtime/simd_text_fuzz.spl`
- Design: Random byte sequences, compare scalar vs SIMD outputs for all kernels
- AC: No divergence on 100K random inputs

**T5.3: Performance Regression Gate** — NOT DONE
- Benchmark harness exists (`string_bench.spl`) but thresholds not measured
- Need to run benchmarks in compiled mode and verify speedup targets

**T5.4: Bootstrap Verification** — DONE (full 5-stage bootstrap passes, all MCP servers compile)

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
| `src/lib/common/string_core.spl` | MOD | Wire to SIMD search/case |
| `src/lib/common/encoding/text_ops.spl` | MOD | Optional WidthIndex path |
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

1. `bin/simple test` — all existing tests pass (no regressions)
2. `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` — self-hosted compiler bootstraps
3. Run benchmark suite — compare scalar vs Tier 1 auto-vec vs Tier 2 C kernel
4. Run fuzz suite — no scalar/SIMD divergence on 100K inputs
5. Manual spot-check: Korean/CJK/emoji strings for correct codepoint counting
6. Verify auto-vec lint fires on target patterns in stdlib code
