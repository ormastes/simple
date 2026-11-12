# rt text slice/find cp-index conversion is O(n) per call: str_split quadratic on non-ASCII, Stage-2 scv_prime sanity hang

**Status:** fix-implemented-verification-pending
**Date:** 2026-11-12
**Severity:** P0 (blocks Stage-2 bootstrap sanity admission on macOS aarch64)
**Host:** macOS aarch64, Stage-2 sanity probe `scv_prime` (p2_add.spl one-binary
native-build with SCV cold inventory init)

## Symptom

The Stage-2 bootstrap sanity probe `scv_prime` hangs: >900 s wall clock,
100% CPU, single-threaded, no output. `sample` of the hung process shows the
entire burn inside two stacks:

```
lib__common__string_core__str_split -> rt_slice -> text_cp_len_bytes / text_cp_to_byte / text_is_ascii_memo
lib__common__string_core__str_split -> rt_text_find -> text_cp_to_byte
```

ASCII-only inputs never reproduce; the hang needs non-ASCII text content in
the file(s) the SCV cold inventory splits.

## Root cause

ADR-005 item 5 makes `s[i]`, `s[a:b]`, `index_of` and friends CODE-POINT
indexed. On non-ASCII heap text every runtime primitive that crosses the
byte/code-point boundary pays a fresh O(n) walk, with no usable memo:

- `rt_slice` (src/runtime/runtime_native.c, string arm): per call runs
  `spl_core_string_is_ascii` (O(n) until the ASCII memo bit is set),
  `spl_text_cp_len_bytes` (O(n)), and `spl_text_cp_to_byte` x2 (O(position)).
- `rt_text_find`: `start` and the answer are code-point indices; per call it
  does `cp_to_byte(start)` (O(start)), a byte search, and `byte_to_cp(hit)`
  (O(hit)).
- `str_split` (src/lib/common/string_core.spl) already jumps between
  separators with one `index_of` + one `substring` per piece, but each piece
  creation and each next-index search re-pays those O(n) conversions.
  Splitting an n-byte non-ASCII string into k pieces is therefore O(n*k) —
  quadratic. During SCV cold inventory init, non-ASCII-bearing source
  file(s) get `str_split` and the probe never finishes.

### The broken cache plumbing (second, latent defect)

src/runtime/runtime_native.c implements `rt_str_cache_cp_count` /
`rt_str_cached_cp_count` / `rt_str_set_ascii_flag` / `rt_str_is_ascii_cached`
(declared in src/runtime/runtime.h), and the SIMD TU
(src/runtime/runtime_simd_utf8.c) has its own copies, all against the layout
constants in src/runtime/runtime_simd_dispatch.h: bit 31 is-ASCII, bit 30
cp-count-valid, bits [29:0] count. The SAME `reserved` word low bits are
owned by `RT_CORE_STRING_FLAG_SHARED=1 / TRANSIENT=2 / SESSION=4 / ASCII=8`
via atomic `fetch_or` in `spl_core_string_is_ascii`. The two layouts collide:

- a cached cp count of 8 sets the ASCII memo on a non-ASCII string;
- flag bits 1/2/4 leak into a stored count (and bit 8 of a count reads as
  "ASCII memoized");
- a cache write does `r = (r & ~mask) | count` with mask covering bits
  [29:0] — clearing the SHARED/TRANSIENT/SESSION flags and defeating
  `rt_string_free`'s refusal to free interned literals.

A struct-field cp-cache was rejected because the 16-byte header is an
explicit ABI: src/runtime/test/rt_freestanding_string_len_abi_selfcheck.c
asserts `offsetof(len)==8` and `offsetof(data)==16`, the struct definition is
duplicated per-TU (RtCoreStringSimd), and allocation sites use
`sizeof(RtCoreString)` only by convention.

## Fix (this change)

1. **Collision-free reserved-word encoding** (runtime_simd_dispatch.h, both
   TUs): ASCII memo stays at bit 3 (`RT_CORE_STRING_FLAG_ASCII`, the only bit
   `spl_core_string_is_ascii` ever sets — now also consulted by the SIMD
   helpers, unifying the two memos). cp-count-valid moves to bit 30, and the
   count occupies bits [29:4] (26 bits, cap 67,108,863 codepoints ≈ 256 MiB
   of 4-byte UTF-8; strings at/above the cap simply never cache and keep the
   pre-fix O(n) cost — conservative non-caching is always safe). Cache writes
   are a compare-and-swap loop that only stores when the valid bit is unset,
   so a cache write can never drop a concurrently-set flag bit.
2. **Wired the cache**: `spl_core_string_cp_len` consults/updates the cache;
   `rt_slice` and `rt_text_find` route their length query through it;
   `rt_text_is_ascii` now uses the memoized `spl_core_string_is_ascii`
   instead of re-scanning per call.
3. **str_split O(n) for non-ASCII haystacks** (src/lib/common/string_core.spl):
   when `text_is_ascii(s)` is false, split walks the UTF-8 bytes once via
   `rt_text_to_bytes` + a byte-exact `str_byte_find` scan, cutting pieces with
   `[u8].slice` and materializing each via `rt_bytes_to_text`. Separator hits
   are byte positions, so pieces are byte-identical to the old cp-indexed
   loop; ADR-005 cp semantics of the public API are unchanged. ASCII
   haystacks keep the existing `index_of`/`str_slice` loop (already O(n)
   total thanks to the ASCII memo).

No pivot memo (last converted (cp,byte) pair) was added: the ABI-pinned
16-byte header has no room for two more words in `reserved`, and a
single-word pivot cannot be encoded safely. Residual cost, documented
honestly: repeated `index_of`/slice on ONE non-ASCII string is still O(n) per
call (one `cp_to_byte` from 0 plus one `byte_to_cp` tail per call) whenever
the query offset is not covered by the ASCII memo or the cp-count cache.
`str_split` no longer triggers that path.

## Rust runtime twin

src/compiler_rust/runtime/src/value/collections.rs has the same shape:
`text_cp_len_bytes`/`text_byte_to_cp`/`text_cp_to_byte` are O(n) walks per
call; `text_byte_to_cp_memo`/`text_cp_to_byte_memo` (lines ~4593-4606) only
route through the memoized ASCII test — they do NOT memoize a position, and
there is no cp-count cache. Find callers at lines 5803/5805 (text_find),
6449, 6494, 6605, 6877. Per project rules the Rust seed is bootstrap-only;
NOT edited. If the native fix proves out, the twin deserves the same
cp-count memo (its `RT_STRING_FLAG_ASCII` at bit 1 of a separate flags word
does not collide).

## Verification

- `cargo check -p simple-runtime` (build.rs compiles runtime_native.c and the
  SIMD TUs via cc): PASS.
- `clang -fsyntax-only` on runtime_native.c, runtime_simd_utf8.c,
  runtime_simd_case.c: PASS.
- Standalone C micro-probe (replicated encoding + CAS helpers): all encoding
  invariants PASS (cache write preserves SHARED/TRANSIENT/SESSION; count 8 no
  longer reads as ASCII memo; flag writes after caching don't corrupt the
  count; cap respected; max count roundtrips). Perf: 1000 repeated cp_len on
  an 8 MiB non-ASCII buffer: 1.118 s uncached vs 0.0011 s cached (~1000x).
- `.spl` change (str_split byte path): NOT executed on this host — no
  admitted compiler (per host limits). Syntax follows existing in-file
  idioms; no execution verification possible here.

## Pending

- Stage-2 bootstrap sanity rerun (`scv_prime` cold inventory init) is the
  end-to-end proof; not run on this host by instruction.
- Repeated index_of/slice on a single non-ASCII string remains O(n)/call
  (no pivot memo; see above).
- Rust twin fix (same cp-count memo), deferred per bootstrap-only rule.
