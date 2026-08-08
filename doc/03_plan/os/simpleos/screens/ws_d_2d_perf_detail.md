# Workstream D — simple-2d Performance: Detail Implementation Plan

Lane: `.spipe/simpleos-screens-render-lane` (AC-7, AC-8).
Parents: `doc/03_plan/os/simpleos/screens_showcase_2d_opt_plan.md` (Workstream D),
`doc/05_design/os/desktop/screen_backend_selection_and_shared_showcase.md` §2.5.
Baseline of record: `doc/09_report/gui_perf_benchmark_2026-07-10.md` — simple-2d
p50 **2389 ms** vs Cairo draw-only **0.032 ms**.
Prior audit: `doc/08_tracking/bug/simd_extern_stub_audit_2026-05-02.md`.

Scope: make the software rasterizer fast. No GPU-backend work, no scene/layout
work beyond what the profile forces.

---

## 0. Verified ground truth (read before editing anything)

Hot path (confirmed by reading the files):

```
src/app/browser/render_adapter.spl:21
  -> src/lib/gc_async_mut/gpu/browser_engine/browser_renderer.spl :: render_html_to_pixel_array
  -> layout.spl / paint.spl
  -> src/lib/common/render_scene/scene.spl
  -> src/lib/gc_async_mut/gpu/engine2d/backend_software.spl        (999 lines — THE rasterizer)
  -> src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl           (620 lines)
  -> src/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows.spl       (35 lines — extern ABI)
  -> src/runtime/runtime_simd_dispatch.c                           (1670 lines, native)
     OR src/compiler_rust/compiler/src/interpreter_extern/simd.rs  (2186 lines, interpreted)
```

### D-F1. Interpreter bridge is O(framebuffer) per span — **interpreted only**
`interpreter_extern/simd.rs:1403 unpack_u32_array` maps **every element** of the
whole array into a fresh `Vec<u32>` (`Value::Array(items) => items.iter().map(...)`).
`:1414 pack_u32_array` rebuilds a **boxed `Value::UInt{width:32}` per pixel**.
Callers `:1486` / `:1511` / `:1513` unpack the entire destination framebuffer for a
span of `count` pixels. The C path is O(count) in place:
`runtime_simd_dispatch.c:1574 rt_engine2d_simd_fill_span_u32` and `:1617
rt_engine2d_simd_copy_span_u32` both call the in-place `rt_engine2d_simd_*_u32`
worker and `return dst`. So the interpreted extern is asymptotically worse than
scalar Simple, and this is the single largest suspected term in the 2389 ms.

### D-F2. Alpha blend has negative SIMD benefit *by construction*
`simd_kernels.spl:372 simd_blend_row` — under `native_pixel_rows_enabled()` it
allocates `dst_row`/`src_row` (`:379-381`), runs an **interpreted gather loop**
(`:382-387`), calls `engine2d_simd_blend_row_u32`, then runs an **interpreted
scatter loop** (`:389-392`). Three interpreted per-pixel passes replace one.
Duplicated twice in the backend:
- `backend_software.spl:621` (extra `active_arch_text() == "x86_64"` gate, gather `:625-628`, scatter `:635-638`)
- `backend_software.spl:764 sw_blend_const_raw_span` (gather `:773-776`, scatter `:779-782`, plus a tail fallback)

`fill_span` / `copy_span` have in-place externs (`simd_native_rows.spl:5,6`,
declared `-> [u32]` returning `dst`); **blend does not**. Worse: even the native
`rt_engine2d_simd_blend_row_u32` (`runtime_simd_dispatch.c:1454`) `malloc`s two
scratch buffers and unbox/rebox each pixel (`:1467-1476`) — it allocates 2N+1
buffers per row.

### D-F3. `simd_fill_row` is slower than scalar
`simd_kernels.spl:348` allocates a native row via `engine2d_simd_fill_row_u32`
then copies it back element-by-element in Simple (`:353-357`). Strictly worse
than `_scalar_fill_row` (`:361`).

### D-F4. Blit is uncovered
`simd_kernels.spl:430 simd_blit_row` unconditionally calls `_scalar_blit_row`
(`:433`). No native path at all.

### D-F5. Damage tracking is write-only
`backend_software.spl:65 dirty_tiles: [bool]`, allocated `:118`, marked at 6
sites (`:154`, `:794 mark_dirty`, `:797-798`, `:804`, `:815`, `mark_span_dirty`),
cleared wholesale in `present()` (`:478-484`). **Read by nobody.**
`src/lib/nogc_sync_mut/compositor/tile.spl:102 get_dirty_tiles()` exists and is
unwired (mirrors in `gc_async_mut/compositor/tile.spl`, `nogc_async_mut/compositor/tile.spl`).

### D-F6. `read_pixels()` copies the framebuffer pixel-by-pixel
`backend_software.spl:487` — interpreted `while` over `w*h`, every call.
Same at `read_pixels_with_source()` just below.

### D-F7. No batching / no back buffer
`backend_software.spl:474 submit_batch()` returns `true` with the comment
"Immediate-mode backend: nothing buffered to flush." No double buffering, no
layer cache, no partial redraw.

### D-F8. Facade inconsistency — two owner trees
- `src/lib/gc_async_mut/gpu/engine2d/simd_kernels.spl` (3 lines) →
  `export use std.nogc_async_mut.gpu.engine2d.simd_kernels.*`
- `src/lib/gc_async_mut/gpu/engine2d/simd_provider.spl` (3 lines) →
  `export use std.nogc_sync_mut.gpu.engine2d.simd_provider.*`

Different owners. `nogc_async_mut/gpu/engine2d/` carries its own
`simd_kernels.spl` + `simd_provider.spl`; only `nogc_sync_mut/gpu/engine2d/`
carries `cpu_simd_session.spl` and `simd_native_rows.spl`. **Canonical owner =
`nogc_sync_mut/gpu/engine2d/`.** `backend_software.spl:21` imports through
`std.gpu.engine2d.simd_kernels`, so today it may resolve to the wrong tree.

### D-F9. Pixel words are BOXED in the native array
`runtime_simd_dispatch.c` treats the `[u32]` payload as `int64_t*` and calls
`engine2d_box_pixel` / `engine2d_unbox_pixel` (`:1467-1476`, `:1552`). Every new
kernel MUST use the same box/unbox discipline (or operate on packed words only
when a future unboxed representation lands). Do not assume `uint32_t*`.

### D-F10. Config hooks that exist today
- `backend_software.spl:75 native_simd_spans: bool`, default `false` (`:95`), set
  `true` at `:100`.
- `simd_kernels.spl:336 native_pixel_rows_enabled()` — cached autodetect
  (`_native_rows_cached` / `_native_rows_detected`, `:333-334`), **no override**.
- `SIMPLE_2D_BACKEND` env, read at
  `gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles_gpu.spl:48`;
  preference order in `gc_async_mut/gpu/engine2d/renderer_select.spl:17`.
- `variants/ui/renderer/<value>/std/gpu/engine2d/renderer_select.spl` overlay.

**There is no way to disable the SIMD span path independently.** Notable because
under the interpreter, disabling it would currently be a *speedup* (D-F1/D-F2).

---

## D0 — Baseline + measurement rig (blocks everything)

**Model:** sonnet. **Depends on:** nothing.

**Objective:** one reproducible, provenance-verified number set, repeated
verbatim after every task below.

### D0.1 Pin the worktree
```bash
cd /home/ormastes/dev/pub/simple
git rev-parse HEAD > /tmp/ws_d_base.sha
git worktree add /run/user/1000/ws_d_bench "$(cat /tmp/ws_d_base.sha)"   # or: jj new + fixed rev
```
All D0 numbers come from the pinned tree. Never compare a number taken from a
dirty working copy against one taken from a clean one.

### D0.2 Verify the binary is the DEPLOYED self-hosted native binary
```bash
readlink -f bin/simple                    # MUST be bin/release/<triple>/simple
bin/simple --version
bin/simple info | head -20                # capability banner
md5sum "$(readlink -f bin/simple)"        # record in the metrics table
```
Record `readlink -f` output in every result row. Size and banner have both lied
before; the row is invalid without the resolved path + md5.

### D0.3 Bench commands
```bash
# Micro kernels + full frame (in-language harness)
bin/simple run test/perf/graphics_2d/bench_2d_gpu.spl            # fn main at :164
bin/simple run test/perf/graphics_2d/bench_2d_tiered_jit.spl
bin/simple run test/perf/graphics_2d/perf_2d_runner.spl

# Cross-check against the C reference (the only external oracle we have)
ls test/perf/graphics_2d/c_reference/
bin/simple test test/perf/graphics_2d/c_vs_simple_2d_spec.spl --no-cache --no-cover-check

# End-to-end GUI frame, the number that owns the 2389 ms
tools/gui_perf_bench/   # follow its README; this is the p50 of record

# RSS
/usr/bin/time -v bin/simple run test/perf/graphics_2d/bench_2d_gpu.spl 2>&1 | grep Maximum
```
Each measurement: **11 runs, discard run 1 (warm-up), report p50 / p99 / max-RSS.**

### D0.4 Metrics table schema (`doc/09_report/ws_d_2d_perf_<task>_<date>.md`)

| task | engine | kernel | px/op | p50 ms | p99 ms | max RSS MB | binary md5 | worktree sha |
|------|--------|--------|-------|--------|--------|------------|-----------|--------------|

Kernel rows, fixed set, every task: `fill`, `copy`, `blend`, `blit`,
`full-frame`, `text`. Engine column ∈ {`native`, `jit`, `interpret`} — see
Measurement Traps for what those words actually mean here.

**Acceptance:** the table exists, filled, for HEAD, on all three engines.
Nothing below merges without a before/after pair in this schema.

---

## D1 — Facade ownership fix (unblocks correct measurement)

**Model:** sonnet. **Depends on:** D0.

**Objective:** one owner tree, so a kernel fix cannot land in a module the
backend does not import.

**Files:**
- `src/lib/gc_async_mut/gpu/engine2d/simd_kernels.spl` — repoint to
  `export use std.nogc_sync_mut.gpu.engine2d.simd_kernels.*`
- `src/lib/nogc_async_mut/gpu/engine2d/simd_kernels.spl`,
  `.../simd_provider.spl` — reduce to facades over `nogc_sync_mut`, deleting the
  divergent bodies (do not leave two implementations).
- `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:21` — leave the
  `std.gpu.engine2d.simd_kernels` import text unchanged; it must now resolve to
  the single owner.

**Acceptance:**
```bash
grep -rn 'fn simd_blend_row' src/lib   # exactly ONE definition, in nogc_sync_mut
bin/simple run test/perf/graphics_2d/bench_2d_gpu.spl   # p50 unchanged ±3%
bin/simple test test/perf/graphics_2d/no_duplication_spec.spl --no-cache
```
Perf-neutral by design; a >3% move means the import was previously resolving
somewhere unexpected — investigate before proceeding.

---

## D2 — In-place `blend_span` extern (Tier 1, highest expected impact)

**Model:** **opus** (native + interpreter kernel work).
**Depends on:** D0, D1. Fixes D-F1, D-F2, D-F9.

### D2.1 New extern ABI
`src/lib/nogc_sync_mut/gpu/engine2d/simd_native_rows.spl` (add beside `:5,:6`):
```simple
pub extern fn rt_engine2d_simd_blend_span_u32(dst: [u32], dst_offset: i64,
                                              src: [u32], src_offset: i64,
                                              count: i64) -> [u32]
pub extern fn rt_engine2d_simd_blend_const_span_u32(dst: [u32], dst_offset: i64,
                                                    count: i64, color: u32) -> [u32]
pub extern fn rt_engine2d_simd_blit_row_u32(dst: [u32], dst_offset: i64,
                                            src: [u32], src_offset: i64,
                                            count: i64) -> [u32]
```
Contract, matching the existing `fill_span`/`copy_span` shape exactly: mutate
`dst` in place, `return dst`, touch only `[dst_offset, dst_offset+count)`,
clamp via the existing `engine2d_span_bounds` helper, **O(count)**.
Note `blit_row` is `memmove` semantics (may alias — scroll-by-copy in D6 needs
overlap safety), while `copy_span` today is `memcpy`-shaped.

### D2.2 C implementation — `src/runtime/runtime_simd_dispatch.c`
Mirror `rt_engine2d_simd_fill_u32` (`:1544`) / `rt_engine2d_simd_fill_span_u32`
(`:1574`) exactly: worker returns `int64_t` count, thin span wrapper returns `dst`.

```c
/* straight-alpha src-over, bit-identical to _scalar_blend_row and to
   rt_engine2d_simd_blend_row_u32's engine2d_blend_into (same floor /255,
   same da==0 => outA=sa path). Boxed words: see engine2d_box_pixel. */
static inline int64_t e2d_blend_one(int64_t dw, int64_t sw);   /* scalar, boxed */

static void e2d_blend_span_scalar(int64_t* d, const int64_t* s, int64_t n);
#if defined(__x86_64__) || defined(_M_X64)
static void e2d_blend_span_sse2(int64_t* d, const int64_t* s, int64_t n);
  /* per 4 px: unpack to 16-bit lanes, _mm_mullo_epi16 by sa/inv_a,
     reciprocal-multiply for /255 (x*0x8081)>>23, _mm_packus_epi16 */
__attribute__((target("avx2")))
static void e2d_blend_span_avx2(int64_t* d, const int64_t* s, int64_t n); /* 8 px */
#elif defined(__aarch64__) || defined(_M_ARM64)
static void e2d_blend_span_neon(int64_t* d, const int64_t* s, int64_t n);
  /* vmovl_u8 / vmlaq_u16 / vqrshrn_n_u16 */
#endif

int64_t rt_engine2d_simd_blend_u32(SplArray* dst, int64_t d_off,
                                   SplArray* src, int64_t s_off, int64_t count) {
    int64_t off = 0, n = 0;
    if (!engine2d_span_bounds(dst, d_off, count, &off, &n)) return 0;
    /* + independent bounds check on src/s_off, clamp n to the smaller */
    int64_t* d = (int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    const int64_t* s = (const int64_t*)(uintptr_t)rt_array_data_ptr(src);
    if (!d || !s) return 0;
#if defined(__x86_64__) || defined(_M_X64)
    if (simd_detect_avx2()) { e2d_blend_span_avx2(d + off, s + s_off, n); return n; }
    e2d_blend_span_sse2(d + off, s + s_off, n); return n;
#elif defined(__aarch64__) || defined(_M_ARM64)
    e2d_blend_span_neon(d + off, s + s_off, n); return n;
#endif
    e2d_blend_span_scalar(d + off, s + s_off, n);
    return n;
}
SplArray* rt_engine2d_simd_blend_span_u32(SplArray* dst, int64_t d_off,
                                          SplArray* src, int64_t s_off, int64_t count) {
    rt_engine2d_simd_blend_u32(dst, d_off, src, s_off, count);
    return dst;                     /* in place, exactly like :1574 / :1617 */
}
```
`blend_const_span` is the same with a broadcast `src` register (no src array —
this is the `sw_blend_const_raw_span` case, the common one for solid fills with
alpha, and it should be the fastest path in the whole rasterizer).
`blit_row` = bounds-check + `memmove` on the boxed words + SIMD only if profiling
shows `memmove` is not already optimal (it usually is; do not hand-roll it).

Runtime dispatch follows the file's existing `simd_detect_avx2()` /
`#if defined(__riscv_vector)` pattern — do not introduce a second dispatch scheme.

**AVX2 must be a runtime check on a `__attribute__((target("avx2")))` function**,
not a compile-time `-mavx2` on the whole TU, or the binary stops booting on
pre-AVX2 hardware.

### D2.3 Interpreter implementation — `interpreter_extern/simd.rs`
The point of this task is that the interpreter stops round-tripping the
framebuffer. Add an in-place path that mutates the rt array buffer directly:
```rust
// NEW: no unpack_u32_array, no pack_u32_array on the dst.
pub fn rt_engine2d_simd_blend_span_u32(args: &[Value]) -> Result<Value, CompileError> {
    // args[0] must be Value::Array(items) -> borrow &mut items
    // clamp offset/count via the same bounds logic as the C span_bounds
    // for i in 0..n { items[d_off+i] = Value::UInt{ value: blend(..), width:32 } }
    // return args[0].clone()   (handle clone, NOT a per-pixel rebuild)
}
```
Requirements:
1. Touch **exactly `count`** elements. No whole-array `Vec<u32>` materialization.
2. Reuse the existing blend arithmetic at `:1553-1571` verbatim so results stay
   bit-identical to `_scalar_blend_row` (`simd_kernels.spl:395`).
3. If `Value::Array` cannot be borrowed mutably in this interpreter's value
   model, **do not fake it** with unpack/pack — file the blocker and instead make
   `native_pixel_rows_enabled()` return `false` under the interpreter (D7), which
   is a measured speedup on its own.
4. Extend the tests at `simd.rs:2136-2185` with in-place span cases: partial
   span, offset span, out-of-bounds clamp, `sa==0` and `sa==255` fast paths.

Apply the same in-place treatment to `rt_engine2d_simd_fill_span_u32` (`:1480`)
and `rt_engine2d_simd_copy_span_u32` (`:1505`) — they have the same D-F1 bug.

### D2.4 Call-site rewrites — delete both blend duplicates
- `simd_kernels.spl:372-393` — replace the entire gather/native/scatter body with
  a single `rt_engine2d_simd_blend_span_u32(dst, offset, src, offset, count)`
  call. Keep `_scalar_blend_row` (`:395`) as the fallback only.
- `simd_kernels.spl:348-359 simd_fill_row` — delete the alloc+copyback branch
  (D-F3); call `rt_engine2d_simd_fill_span_u32` in place, else `_scalar_fill_row`.
- `simd_kernels.spl:430-433 simd_blit_row` — route to
  `rt_engine2d_simd_blit_row_u32` (D-F4).
- `backend_software.spl:621-643` — **delete** the whole x86_64-gated gather/
  scatter block and its `active_arch_text()` gate (arch dispatch belongs in C);
  call the new span extern. Keep `record_simd_alpha_hit()`.
- `backend_software.spl:764-792 sw_blend_const_raw_span` — **delete** the gather,
  scatter, and short-row tail; call `rt_engine2d_simd_blend_const_span_u32`.
  Keep the `_span_safe_count` guard and the scalar fallback.
- `simd_kernels.spl:477 alpha_blend_span` / `:484 _scalar_alpha_blend_span` —
  re-point at the new span kernel.

The `# cpu-lane-loop-ok:` comments on those loops go with the loops.

**Acceptance:**
```bash
grep -c 'engine2d_simd_blend_row_u32' src/lib src/app -r   # expect 0 in hot paths
bin/simple run test/perf/graphics_2d/bench_2d_gpu.spl
bin/simple test test/perf/graphics_2d/c_vs_simple_2d_spec.spl --no-cache --no-cover-check
bin/simple test test/perf/graphics_2d/cpu_simd_spec.spl --no-cache --no-cover-check
cargo test -p simple-compiler interpreter_extern::simd   # from src/compiler_rust
```
Expected: `blend` p50 **≥10x faster interpreted**, ≥2x native. `full-frame` p50
must move materially (this is the biggest single term). Pixel output must be
**byte-identical** to the pre-change framebuffer — dump both and `cmp`.

---

## D3 — Damage-driven present (Tier 1)

**Model:** sonnet. **Depends on:** D2. Fixes D-F5, part of D-F7.

**Objective:** stop presenting the whole framebuffer when 2% of it changed.

**Files:** `backend_software.spl` (`:65`, `:118`, `:474`, `:478`, `:794`),
`src/lib/nogc_sync_mut/compositor/tile.spl:102`.

1. Add `me get_dirty_rects() -> [Rect]` to the software backend: scan
   `dirty_tiles` (already correctly marked at all 6 sites) into tile rects.
2. Add `me present_rect(x: i32, y: i32, w: i32, h: i32)` and make `present()`
   (`:478`) = `for r in merge(get_dirty_rects()): present_rect(r)`, then clear —
   preserving today's clear semantics exactly.
3. **Region merge heuristic:** merge rects `a`,`b` when
   `area(union(a,b)) <= (area(a) + area(b)) * k`, `k = 1.5`. Cap the list at
   `RECT_CAP` (start 16, tunable 8..32); past the cap, collapse everything to the
   bounding box of the remainder. Full-screen invalidate = one rect.
4. Wire `tile.spl:102 get_dirty_tiles()` as the compositor-side source of the
   same rect list; `mark_dirty_region` (`:93`) is the widget-layer entry point,
   so a widget bbox invalidation feeds tile marking without new plumbing.
5. Widget-layer bbox invalidation: any draw op already calls `mark_span_dirty`
   (`:815`) / `mark_pixel_dirty`; ensure text and image draws do too.

**Acceptance:** `tools/gui_perf_bench/` UI-frame scenario (small cursor/caret
change) p50 **10-100x** faster; full-repaint frame p50 unchanged ±3%.
Add a spec asserting `get_dirty_rects()` is empty right after `present()` and
non-empty after exactly one `mark_dirty`.

---

## D4 — Premultiplied ARGB + opaque fast paths + bulk `read_pixels`

**Model:** sonnet (kernel edits pair with D2 opus work). **Depends on:** D2.
Fixes D-F6. Tier 2.

1. **Internal format = premultiplied ARGB8888.** Convert on ingress
   (`Layer::from_pixels`, `compositor.spl:48`) and egress (`read_pixels`).
   Blend then loses the `/out_alpha` divide in `_scalar_blend_row:390-393` and
   its C twin — that divide is the hot instruction in the current kernel.
2. **Per-surface `opaque: bool`** on the software backend struct (near `:65`).
   When `opaque` and `sa == 255`, `blend_span` degrades to `copy_span`; select
   the blitter **once per span**, not per pixel (Skia pattern), keyed by
   `(op, src_opaque, dst_opaque, has_mask)` — a small pixman-style fast-path
   table in C, not a chain of per-pixel `if`s.
3. **Clip/bbox early-out** before the span loop, so fully-clipped spans cost O(1).
4. **Bulk `read_pixels`** (`backend_software.spl:487` and
   `read_pixels_with_source` below it): replace the per-pixel `while` with
   `rt_engine2d_simd_copy_span_u32(copy, 0, self.buf, 0, w*h)`.

**Acceptance:** `blend` p50 further 2-4x; `read_pixels` p50 ≥10x (it becomes a
`memcpy`). Colour-correctness spec: round-trip premultiply/unpremultiply of all
256 alpha values against the straight-alpha reference, tolerance ±1 LSB, and the
existing `c_vs_simple_2d_spec.spl` must still pass.

---

## D5 — Command batching / single back buffer

**Model:** sonnet. **Depends on:** D3. Fixes D-F7. Tier 3.

`submit_batch()` (`backend_software.spl:474`) becomes real: accumulate span ops,
sort by destination row, flush on `present()`. **One back buffer only** — in a
software renderer triple buffering costs more memcpy than it saves; present the
damage rects into the mmap'd surface zero-copy (no intermediate `read_pixels`).

**Acceptance:** `full-frame` p50 improves or is flat; max-RSS must not grow by
more than one framebuffer. If p50 is flat, this task is a **revert** (see D9).

---

## D6 — Per-window backing store, occlusion culling, scroll-by-copy

**Model:** **opus** (compositor backing store). **Depends on:** D3, D4. Tier 1/3.

**Files:** `src/os/compositor/wm_core.spl` (77 lines; `raise_to_top:36`,
`apply_resize:52` are the existing geometry ops),
`src/lib/gc_async_mut/gpu/engine2d/compositor.spl`
(`Layer:34/48`, `_layer_bounds:196`, `layer_rects_overlap:204`,
`compositor_pick_topmost:211`).

1. **Per-window backing store:** each `Layer` owns its pixels (`from_pixels:48`
   already implies this); an unchanged window re-composites by `copy_span`, never
   by re-running its paint.
2. **Occlusion culling:** walk layers top-down; subtract each opaque layer's rect
   from the remaining damage region. `layer_rects_overlap:204` is the primitive;
   `_layer_bounds:196` gives the rects. Skip a layer entirely when its
   contribution is empty.
3. **Scroll-by-copy (GDI pattern):** on a scroll of `dy`, `memmove` the retained
   region within the backing store (`rt_engine2d_simd_blit_row_u32`, overlap-safe
   per D2.1) and damage **only the revealed strip**. `simd_kernels.spl:531
   simd_scroll_region` / `:569 _scalar_scroll_region` already exist — route them
   through the new in-place blit and make them mark the strip.

**Acceptance:** terminal-scroll scenario in `tools/gui_perf_bench/` p50 ≥10x
faster; a fully-occluded window costs ~0 in the frame profile (assert via the
SIMD hit counters, `record_simd_*_hit`).

---

## D7 — Glyph atlas + masked text blit

**Model:** sonnet. **Depends on:** D2, D4. Tier 2.

- A8 coverage atlas, **shelf packer** (LRU eviction is a later task, not now —
  do not build eviction before the atlas is measured full).
- Rasterize each glyph once; a text run becomes N masked blits from the atlas.
- Masked SIMD blit kernel: `rt_engine2d_simd_blend_mask_a8_u32(dst, dst_off,
  color, mask: [u8], mask_off, count)` — same in-place contract as D2.1. The
  backend already carries `mask_buf` / `mask_w` / `mask_h`
  (`backend_software.spl:470-472`), so the mask plumbing exists.
- Sparse coverage-delta AA (FreeType / stb_truetype pattern) for the rasterizer;
  scanline AET for general paths is a follow-on, filed not built, unless the
  profile demands it.

**Acceptance:** `text` p50 **10-50x**; glyph cache hit rate >95% on the showcase
text scenario; rendered text pixel-diff vs pre-change ≤1 LSB per channel.

---

## D8 — SIMD configurability (AC-8)

**Model:** sonnet. **Depends on:** D2. Fixes D-F10.

**Setting:** `screen_simd` (config) / `SIMPLE_2D_SIMD` (env) ∈
`auto | off | sse2 | avx2 | neon`, env wins over config, config wins over
autodetect. Plus **per-kernel toggles**:
`SIMPLE_2D_SIMD_FILL|COPY|BLEND|BLIT` ∈ `auto|off`.

**Plumbing:** `simd_kernels.spl:336 native_pixel_rows_enabled()` has no override
today — its `_native_rows_cached` / `_native_rows_detected` memo (`:333-334`) is
set purely from `detect_simd_level()` (`:126`). Change to:

```simple
pub fn native_pixel_rows_enabled() -> bool:
    if _native_rows_detected:
        return _native_rows_cached
    val forced = env_get("SIMPLE_2D_SIMD")           # then config screen_simd
    if forced == "off":
        _native_rows_cached = false
    elif forced == "sse2" or forced == "avx2" or forced == "neon":
        _native_rows_cached = true                   # + pin the level for C dispatch
    else:
        val level = detect_simd_level()
        _native_rows_cached = level == SimdLevel.Neon or level == SimdLevel.Avx2
                              or level == SimdLevel.Sse42 or level == SimdLevel.Rvv
    _native_rows_detected = true
    _native_rows_cached
```
Add `pub fn simd_kernel_enabled(kernel: text) -> bool` for the per-kernel gates
and consult it at each of the four call sites. Forced level must also reach the C
side (a `rt_simd_force_level(i64)` setter, honoured by `simd_detect_avx2()`),
otherwise `sse2` and `avx2` are indistinguishable.

`backend_software.spl:100`'s unconditional `native_simd_spans = true` becomes
`= simd_kernel_enabled("spans")`.

**The interpreted default is chosen BY MEASUREMENT, not by assumption.** Run the
D0 table for `SIMPLE_2D_SIMD=auto` vs `off` on the interpreter after D2; whichever
wins becomes the default, and the winning table is cited in the commit message.

**Acceptance:** each of the 5 levels × 4 kernel toggles produces
byte-identical output; `off` and `auto` both bench; a spec asserts the env
override actually changes `native_pixel_rows_enabled()` (beware the memo — the
spec must run in a fresh process per value, see traps).

---

## D9 — Regression gate (standing rule, applies from D1 onward)

**Model:** sonnet. **Depends on:** D0.

1. Every task commit ships a `doc/09_report/ws_d_2d_perf_<task>_<date>.md` with
   the **full D0.4 table**, before and after, all three engines.
2. A task that does not improve its stated target metric by its stated magnitude
   is **reverted or filed as a bug** — never merged silently and never
   re-scoped after the fact to match the number it got.
3. Any other row regressing >5% blocks the merge until explained in the report.
4. `test/perf/graphics_2d/report_spec.spl` gains an assertion on the recorded
   p50 ceiling per kernel, so a later change that undoes D2 fails a test rather
   than a memory.

---

## Measurement traps (this repo has a documented history of false-green benchmarks)

1. **`SIMPLE_EXECUTION_MODE=native` is NOT a mode.** Everything except
   `interpret` is JIT. There is no env var that selects the native/AOT path — you
   get native only by building and running a native binary. A row labelled
   "native" that was produced by setting that variable is a fabricated row.
2. **`simple test` can silently delegate to the Rust seed child.** A green run
   is not proof the self-hosted binary executed. Set
   `SIMPLE_TEST_RUNNER_RUST=1` deliberately when you want the seed, and
   otherwise verify which binary actually ran.
3. **The test daemon freezes env selectors.** `SIMPLE_2D_SIMD` /
   `SIMPLE_2D_BACKEND` set after the daemon started are stale, not empty — the
   daemon will happily bench the default while you believe you set `off`.
   `test_daemon_stop` before any env-matrix run, and use `--no-cache
   --no-cover-check` (concurrent runs also race a shared manifest → "0 tests
   found").
4. **`native_pixel_rows_enabled()` memoizes on first call** (`simd_kernels.spl:333`).
   An in-process matrix over `SIMPLE_2D_SIMD` values measures the FIRST value
   five times. One fresh process per value.
5. **In-language benchmarks have fabricated numbers before.** Cross-check every
   kernel row against `test/perf/graphics_2d/c_reference/` and against wall-clock
   `/usr/bin/time`. A number with no external corroboration is a claim.
6. **Verify binary provenance, not source hashes.** `readlink -f bin/simple` has
   pointed at a stale scratch build while the source md5 matched.
7. **Measurement requires a pinned worktree.** The same spec and binary have
   produced 25/3 and 28/0 from an unpinned tree.
8. **Parallel agent sessions edit these files.** Check `git status` + mtime
   before attributing a delta to your own change.
9. **Exit 255 with no output is a 60 s timeout**, not a crash; exit 143 is a
   SIGTERM truncation that can fake a plausible diff.
10. **Sabotage-test the implementation, not the shim.** To prove a bench actually
    exercises the new kernel, corrupt the C kernel body and confirm the bench
    output changes — not just that the extern is reachable.

---

## Dependency graph

```
D0 ──> D1 ──> D2 ──> D3 ──> D5
                │      └──> D6
                ├──> D4 ──> D6
                ├──> D7
                └──> D8
D0 ──> D9 (standing)
```

Models: **opus** = D2 (native + interpreter kernels), D6 (compositor backing
store). **sonnet** = D0, D1, D3, D4, D5, D7, D8, D9.
