# engine2d SIMD blend span kernel — design plan (2026-08-07)

Status: DESIGN ONLY. No Rust/C source touched by this doc. Follow-on from
`doc/08_tracking/bug/engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md`
§3 ("Still missing: an in-place blend span kernel"). §2 of that bug doc was
retracted this session as a false positive — see
`doc/03_plan/ui/perf/engine2d_simd_fill_span_colour_boxing_fix_plan_2026-08-07.md`
for that retraction's evidence. §3's finding is unaffected and still stands.

## 1. Why blend needs different treatment than fill/copy — verified, not assumed

Read `src/runtime/runtime_simd_dispatch.c` around all three kernels
(`rt_engine2d_simd_fill_span_u32` L1574-1578, `rt_engine2d_simd_copy_span_u32`
L1617-1622, `rt_engine2d_simd_blend_row_u32` L1454-1490) to settle this rather
than assume it.

`SplArray` element storage for this engine is **not raw pixel bits** — it is a
tagged 64-bit word: `engine2d_box_pixel(u32 px) = (i64)px << 3`,
`engine2d_unbox_pixel(i64 v) = (u64)v >> 3` (L663-669). That tag is why:

- **`fill_span`** never touches per-element pixel math: it boxes the fill
  colour **once** (`engine2d_box_pixel` on the scalar `color`, L1551) and then
  writes that single boxed word into every slot in `data+off..data+off+n`
  directly via the SSE2/AVX2/RVV/NEON fill loops (L1544-1572). No unboxing
  needed because no per-element arithmetic happens on the tag.
- **`copy_span`** never touches pixel bits either: it's a `memmove` of the raw
  tagged words as opaque 64-bit values (L1591-1614, `engine2d_copy_u32_rvv`,
  `memmove`). Copy doesn't care what the tag encodes.
- **`blend_row`** genuinely must read the real 8-bit ARGB channels of BOTH
  `dst[i]` and `src[i]` to compute Porter-Duff src-over per pixel — that part
  of the difference is architectural, not laziness. But the specific mechanism
  chosen — `malloc` two full-length scratch buffers, unbox everything into
  them, call the vectorized `engine2d_blend_into` on the *untagged* buffers,
  then box every result back into `out[i]` (L1465-1483) — is **not** required
  by that architectural fact. The existing scalar fallback three lines below
  (L1484-1488, taken whenever either `malloc` fails) already proves the
  unbox→blend→box sequence can be done **per element, in place, with zero
  heap allocation**:
  ```c
  uint32_t dst_pixel = engine2d_unbox_pixel(dst_data[i]);
  uint32_t src_pixel = engine2d_unbox_pixel(src_data[i]);
  out[i] = engine2d_box_pixel(engine2d_blend_pixel(src_pixel, dst_pixel));
  ```
  The only reason the fast path needs `malloc` at all is that
  `engine2d_blend_into`/`_avx2`/`_sse2` (L1088-1318) are written to consume
  contiguous **untagged** `int64_t*` buffers for SIMD lane math — they were
  never given tagged-word-aware entry points, and `blend_row` was written to
  allocate-and-return a **new** array (mirroring `copy_row`'s shape) rather
  than an **in-place span** (mirroring `fill_span`/`copy_span`'s shape).
  Confirming this further: the Rust-seed **interpreter** bridge for
  `rt_engine2d_simd_blend_row_u32`
  (`src/compiler_rust/compiler/src/interpreter_extern/simd.rs:1543-1560`)
  computes src-over directly on `u32` values with no scratch buffer at all —
  the malloc is purely an artifact of the native C dispatch's implementation
  choice, not something blending fundamentally requires.

**Verdict: blend is architecturally different from fill/copy in one respect
(it must read two operands' real pixel channels, not just move/stamp tagged
words), but the malloc+full-buffer-unbox/rebox design is unwritten-in-place,
not architecturally forced.** An in-place span kernel is straightforwardly
possible using the same per-element unbox→`oracle_src_over`→box sequence the
scalar fallback already uses, chunked through small on-stack buffers (or SIMD
lanes) to still get vectorization, with **zero heap allocation** — matching
fill_span/copy_span's no-malloc, write-into-`dst`-in-place convention.

## 2. Pixel format convention (ground truth)

This engine already commits to **straight (non-premultiplied) alpha**,
`KERNEL_FORMAT_ARGB8888_STRAIGHT` (`src/lib/common/gpu/engine2d/kernel_registry.spl:47`,
value `0`). The compositing formula is defined once, authoritatively, in
`src/lib/common/gpu/engine2d/scalar_oracle.spl`:

```
fn oracle_src_over(s: i64, d: i64) -> i64:
    val sa = oracle_alpha(s)
    if sa == 255: return s
    if sa == 0: return d
    val da = oracle_alpha(d)
    val inv_a = 255 - sa
    val dst_weight = (da * inv_a) / 255      # truncating floor division — normative
    val out_a = sa + dst_weight
    val out_r = (oracle_red(s)*sa + oracle_red(d)*dst_weight) / out_a
    val out_g = (oracle_green(s)*sa + oracle_green(d)*dst_weight) / out_a
    val out_b = (oracle_blue(s)*sa + oracle_blue(d)*dst_weight) / out_a
    oracle_pack(out_a, out_r, out_g, out_b)
```

(ARGB layout: alpha bits 24-31, red 16-23, green 8-15, blue 0-7 — same as
`engine2d_blend_pixel`/`engine2d_blend_into` in the C file, L1156 onward.) Both
new kernels must be bit-exact against this formula — the division is
**truncating floor**, not round-half-up; "fixing" that turns a parity test
into a mass pixel diff (see `doc/04_architecture/ui/rendering/exact_8bit_pixel_formula.md`
§0/§3, cited at the top of `scalar_oracle.spl`).

`oracle_src_over_image` (span-of-src blend) and `oracle_src_over_const`
(single-colour blend, `src/lib/common/gpu/engine2d/scalar_oracle.spl:189-212`)
are the exact per-kernel oracles the two new native kernels below must match.

## 3. Proposed signatures

Following `fill_span`/`copy_span`'s exact convention: in-place span, offset +
count, returns the mutated `dst` array (native ABI mutates in place; the
interpreter bridge re-wraps the `Arc` value and returns it, same as
`rt_engine2d_simd_fill_span_u32`/`copy_span_u32` already do).

```c
/* src/runtime/runtime_simd_dispatch.c */

/* Blend src[src_off..src_off+n) over dst[dst_off..dst_off+n) in place,
 * straight-alpha src-over (oracle_src_over). No malloc. */
SplArray* rt_engine2d_simd_blend_span_u32(SplArray* dst, int64_t dst_off,
                                          SplArray* src, int64_t src_off,
                                          int64_t count);

/* Blend one constant colour over dst[offset..offset+count) in place,
 * straight-alpha src-over (oracle_src_over_const). No src array, no malloc. */
SplArray* rt_engine2d_simd_blend_const_span_u32(SplArray* dst, int64_t offset,
                                                int64_t count, int64_t const_color);
```

Simple-side signatures (matching the doc's requested form):

```
extern fn rt_engine2d_simd_blend_span_u32(dst: [u32], dst_off: i64, src: [u32], src_off: i64, len: i64) -> [u32]
extern fn rt_engine2d_simd_blend_const_span_u32(dst: [u32], dst_off: i64, len: i64, const_color: i64) -> [u32]
```

### Implementation sketch (C, span-bounded like fill/copy)

Both kernels reuse `engine2d_span_bounds` for clamping (same as
`rt_engine2d_simd_fill_u32`/`copy_u32`), then iterate directly over the
**tagged** `int64_t*` words already in `dst`'s (and `src`'s) backing storage —
unbox, composite via the oracle-equivalent `engine2d_blend_pixel`, box, store
back — no `malloc`/`free`, matching the scalar-fallback sequence already
proven correct at L1484-1488:

```c
SplArray* rt_engine2d_simd_blend_span_u32(SplArray* dst, int64_t dst_off,
                                          SplArray* src, int64_t src_off,
                                          int64_t count) {
    int64_t d_off = 0, n = 0;
    if (!engine2d_span_bounds(dst, dst_off, count, &d_off, &n)) return dst;
    int64_t s_off = 0, sn = 0;
    if (!engine2d_span_bounds(src, src_off, n, &s_off, &sn)) return dst;
    if (sn < n) n = sn;
    int64_t* dst_data = (int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    const int64_t* src_data = (const int64_t*)(uintptr_t)rt_array_data_ptr(src);
    if (!dst_data || !src_data) return dst;
    for (int64_t i = 0; i < n; i++) {
        uint32_t s = engine2d_unbox_pixel(src_data[s_off + i]);
        uint32_t d = engine2d_unbox_pixel(dst_data[d_off + i]);
        dst_data[d_off + i] = engine2d_box_pixel((uint32_t)engine2d_blend_pixel(s, d));
    }
    return dst;
}
```

`rt_engine2d_simd_blend_const_span_u32` is the same loop with `s` fixed
(unbox `const_color` once) and an `sa == 0` early-return over the whole span
(mirrors `oracle_src_over_const`'s guard). A SIMD fast path (chunked
on-stack unbox buffers feeding `engine2d_blend_into_avx2`/`_sse2`, e.g. 64
pixels at a time, well within a cache line — never a heap `malloc`) is an
optional follow-up once the scalar in-place version is verified bit-exact;
this plan does not require it for a correct v1.

## 4. Extern registration (Rust seed)

Mirror exactly how `rt_engine2d_simd_fill_span_u32`/`copy_span_u32` are wired:

1. **Interpreter bridge** — `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`.
   New functions `rt_engine2d_simd_blend_span_u32`/`rt_engine2d_simd_blend_const_span_u32`
   next to `rt_engine2d_simd_copy_span_u32` (~L1505-1528), following the same
   `unpack_u32_array` → bounds-clamp → compute → `pack_u32_array(dst)` shape.
   The compositing body can reuse the existing `rt_engine2d_simd_blend_row_u32`
   per-pixel logic (L1543-1560ff, already does `oracle_src_over` directly on
   `u32` with no scratch buffer) instead of writing new blend math.
2. **Registry insert** — `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`,
   next to the existing `insert_simple!("rt_engine2d_simd_fill_span_u32", ...)`
   / `insert_simple!("rt_engine2d_simd_copy_span_u32", ...)` lines (~L1708-1711):
   add `insert_simple!("rt_engine2d_simd_blend_span_u32", simd::rt_engine2d_simd_blend_span_u32);`
   and the `_const_span_` sibling.
3. **Native symbol table** — the build-generated
   `runtime_symbol_entries.rs` (build script output under
   `target/release/build/simple-runtime-*/out/`) picks up the new C symbols
   automatically from the runtime build; no manual edit, just confirm the
   `#[link_name = "rt_engine2d_simd_blend_span_u32"]` entry appears after a
   rebuild, the same way `copy_span_u32`/`fill_span_u32` already do.

## 5. Verification plan

Follow `test/01_unit/lib/nogc_sync_mut/gpu/engine2d/simd_isa_provider_spec.spl`'s
established pattern exactly (canonical-hash bit-exactness, `describe`/`it` +
`oracle_hash_span`):

1. Import `oracle_src_over_image`, `oracle_src_over_const`, `oracle_hash_span`
   from `scalar_oracle.spl` alongside the new externs.
2. For several spans (small: 4, 64; large: 4096; boundary: offset near array
   end, zero-length, fully-transparent src, fully-opaque src) build matched
   `dst`/`src` buffers with the spec file's existing `filled_random`/LCG
   helper, run both `oracle_src_over_image`/`oracle_src_over_const` (on a copy)
   and the new native kernel (on another copy), and assert
   `oracle_hash_span(oracle_buf, 0, n) == oracle_hash_span(native_buf, 0, n)` —
   bit-exact, not approximate.
3. Add one `describe` block per kernel:
   `"SIMD ISA provider — blend_span vs canonical hashes (lane P?)"` and
   `"... blend_const_span vs canonical hashes"`, next to the existing
   src_over_image/mask_src_over block (L186-221 of the spec file).
4. Regression-guard the specific edge cases the retracted §2 investigation and
   the surviving §3 finding both care about: `sa==0` (no-op), `sa==255`
   (verbatim copy of src, matching `oracle_src_over`'s fast path), and a
   zero-length span (must not touch `dst` at all, matching `fill_span`'s
   `count<=0` early return).

## 6. Rust-seed rebuild required — schedule as its own isolated session

This design touches `src/runtime/runtime_simd_dispatch.c` (native C) and
`src/compiler_rust/compiler/src/interpreter_extern/{simd.rs,mod.rs}` (Rust
seed). Per `feedback_extern_bootstrap_rebuild.md` and `.claude/rules/bootstrap.md`,
any new extern requires a full seed rebuild (`--full-bootstrap`) before the
symbol is reachable from `bin/release/<triple>/simple`, and per this session's
established precedent (WS-D D2.1/D2.2 in the source bug doc), that rebuild
should **not** be done opportunistically inside an unrelated session — it
needs its own isolated session so the rebuild's correctness (and any fallout,
e.g. the currently-tracked Stage 3 `ByteOrder`/`Effect` blockers noted in
`.claude/rules/bootstrap.md`) can be verified in isolation rather than folded
into a design-only change. This plan is implementation-ready but
**intentionally not implemented here**.
