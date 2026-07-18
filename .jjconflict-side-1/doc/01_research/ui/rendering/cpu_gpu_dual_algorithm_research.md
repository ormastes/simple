<!-- opus-research 2026-07-07 -->
# CPU vs GPU Dual-Algorithm Rendering — Research

**Companion design:** `doc/05_design/ui/rendering/cpu_gpu_dual_algorithm_design.md`.
**Companion plan:** `doc/03_plan/ui/rendering/cpu_gpu_dual_algorithm_plan.md`.
**Anchors verified 2026-07-07** against the working tree; unverifiable items are marked ASSUMPTION.

**Thesis (user mandate).** GUI/rendering logic must use **different algorithms per lane**. On the
interpreted CPU lane, per-element / per-pixel loops are the wrong shape — this week's measurements
prove per-pixel FFI hops and interpreted byte-array reads cost 10x a single native `split()`, and
scalar `clear`/`read_pixels` loops run 830–897 ms/frame at 720p. On the GPU lane the *same* op is
correctly a data-parallel kernel. The two lanes should not share one algorithm; they should share a
**parity oracle** (§3) and select the lane-appropriate algorithm from a declared capability set.

---

## 1. Current divergence points — the same logical op, two implementations

The engine2d backend set already implements each Draw-IR op twice: once as a **CPU reference**
(scalar rasterizer) and once as a **GPU kernel**. Today these are held together by the D2 parity
oracle, not by a declared "algorithm set" abstraction.

| Op | CPU-lane impl (scalar) | GPU-lane impl (data-parallel) | Parity status |
|---|---|---|---|
| `clear` | `backend_software.spl:137-146` — `while i<total` scalar fill + dirty-span loop | `kernel_clear` (`backend_metal_msl.spl`, 1 thread/pixel) | BIT-EXACT (D2 matrix) |
| `draw_rect_filled` | `backend_software.spl` span fill | `kernel_draw_rect_filled` | BIT-EXACT |
| `draw_circle_filled` | `backend_software.spl:280` per-row isqrt disk | `kernel_draw_circle_filled` (distance check) | reconciled → **SW** canonical, Metal-exact |
| `draw_triangle_filled` | `backend_software.spl:322` integer barycentric | `kernel_draw_triangle_filled` (barycentric) | reconciled → **SW** canonical, Metal-exact |
| `draw_gradient_rect` | emu/sw integer lerp | `kernel_draw_gradient_rect` (vertical) | opaque repr. BIT-EXACT |
| `draw_line` | `sw_bresenham` lean single-guard | `kernel_draw_line` (1 thread/step) | thin BIT-EXACT; thick DIVERGENT, deferred |
| `blit`/`draw_image` | scalar copy | `kernel_blit_image` (buffer(2) source) | BIT-EXACT |
| `draw_text` | `backend_software.spl:364-402` nested 5x7 glyph loops | *(no text kernel — CPU only)* | **SW** canonical (emu is a placeholder box stub) |
| `blur`/`shadow` | `backend_emu_adv.spl:41-76` O((2r+1)²) tap loop | *(no kernel)* | CPU only |

**Sources.** MSL kernel roster: `backend_metal_msl.spl:21-32` (37 kernel/buffer decls). Per-op
equality verdicts and canonical winners: `draw_ir_multibackend_design.md` §"D2 op-consolidation
roadmap" (the empirical equality matrix). The CPU reference **is** the parity oracle: `SharedRaster`
= `backend_emu.spl` (23 ops) + `backend_emu_adv.spl` (5 ops), and every backend's accelerated path
"must match it bit-for-bit on readback" (`draw_ir_multibackend_design.md` §3b).

### CPU paths still running per-element interpreted loops on hot paths

From the measured perf plan `doc/03_plan/ui/perf/gui_web_2d_perf_fix_plan.md`:

- **`clear` / `read_pixels` bulk** — scalar `while` loops (`backend_software.spl:137-146`, and the
  readback copy). 50–200x achievable via memset/memcpy but **BLOCKED** on the mutable-array-extern
  bridge (perf plan N5; `doc/08_tracking/bug/cpu_simd_mutable_array_extern_wiring_2026-05-31.md`,
  OPEN). The 830–897 ms/frame @720p figure is this class.
- **`draw_blur_rect`** — O((2r+1)²) tap loop, 70.6 s for one 160×90 r=6 blur; 2D-1 inlined the
  channel math (~12M interpreted dispatches removed, LANDED `7f549df2`); separable 2-pass is N2
  (deferred, pixel-changing, D2-gated).
- **`draw_gradient_rect`** — 6.16x per-px vs a plain fill (perf plan N4).
- **`draw_text`** — ~547 µs/char, per-glyph allocation not pixel-bound (`glyph_bitmap_5x7.spl:97-107`;
  perf plan 2D-5).
- **web `compute_styles` / `parse_html`** — superlinear; the fix that won under the interpreter was
  **one native `split()`** event scan, not a per-position `substring` walk and not a `[u8]`
  byte-array walk (measured **~10x worse**) — perf plan N1, and
  `doc/08_tracking/bug/css_bytes_helpers_dead_code_2026-07-07.md`.

### The "SIMD" divergence is currently fake

`src/lib/gc_async_mut/gpu/engine2d/simd_kernels.spl` is a one-line facade
(`export use std.nogc_async_mut.gpu.engine2d.simd_kernels.*`). Real NEON/AVX2 kernels exist at
`nogc_sync_mut/gpu/engine2d/simd_kernels.spl:333-378` (real `extern`-backed intrinsics; also
`rt_engine2d_simd_*`), but the `cpu_simd` *backend selector* is a **bare alias of scalar `cpu`**
(`engine.spl:271-279` instantiates the byte-identical `CpuBackend.create()` for both); the only
"SIMD" signal is `record_simd_*_hit()` telemetry with no vector dispatch behind it. This is the
canonical fake-evidence pattern (`draw_ir_multibackend_design.md` §5 / D4; perf plan N6). It is a
*third* algorithm lane (SIMD-CPU) that is declared but not wired.

### Offload state (the per-frame vehicle)

- **Persistent sessions** — `Engine2D` created once, `clear`+redraw per frame: raster-bound
  **176x–684x** vs per-frame create/shutdown (commit `a7b57550`;
  `doc/00_llm_process/feature_expert/wm_gui_window_drawing/skill.md:300-307`).
- **Batched Metal buffer FFI** — `rt_metal_buffer_upload` / `rt_metal_buffer_download` /
  `rt_metal_set_bytes` (`backend_metal_runtime_ops.spl:2-4`), one FFI shot per frame. **These are
  implemented and are a preserved fast path** (`draw_ir_multibackend_design.md` §Perf anchors).
- **One-call readback** — `rt_u32s_from_raw` (device→host, works) vs `rt_write_u32s_to_raw`
  (host→device, **declared at `backend_metal_runtime_ops.spl:6` but the runtime symbol is not
  implemented** → `SIMPLE_ONE_CALL_READBACK=1` crashes with `unknown extern function:
  rt_write_u32s_to_raw`; perf plan N7 / Web Rank 1). Seed/runtime-extern change, off the pure-Simple
  path.

---

## 2. GPU dictionary / lookup-table state — feasibility verdict

**Verdict: NO GPU-side hash/dict/lookup-table primitive exists today, but a buffer-backed LUT is
feasible on the deployed interpret-mode binary with NO new externs — because it is upload-only.**

Evidence for absence:
- Grep of the MSL/CUDA/Intel kernel sources for `palette|lut|lookup|hash|dict|colormap|indexed` found
  **zero** kernel-side lookup structures. The only hit is an *aspirational comment*:
  `backend_intel_kernels.spl:132` — "For production use, a glyph atlas would be pre-uploaded to GPU
  memory."
- The former browser-private CPU glyph atlas was removed; browser text now owns no parallel
  compositor path. No browser-private atlas is uploaded to device memory or indexed by a kernel.

Evidence the primitive is **buildable without a seed change**:
- The MSL kernels already bind multiple device buffers — `buffer(0)` framebuffer, `buffer(1)`
  constant params (via `rt_metal_set_bytes`), `buffer(2)` source for blit
  (`backend_metal_msl.spl:16-20`). A LUT is just **one more device buffer**.
- Uploading a host array into a device buffer already works via `rt_metal_buffer_upload`
  (`backend_metal_runtime_ops.spl:3`, a preserved fast path). Upload is **host→device**, so it does
  **not** touch the unimplemented `rt_write_u32s_to_raw` (that gap is device→host writeback of an
  arbitrary `[u32]`, a different direction).
- A GPU dict/lookup is therefore realizable as **an MSL string edit + an extra bound buffer** —
  no new `extern`, honoring the "no new externs without a cdylib route" constraint.

Minimal GPU dict — two viable kernel-side shapes (both pure MSL, no atomics needed for read-only
tables):
1. **Sorted-array binary search.** Upload `[count, key₀..keyₙ, val₀..valₙ]` sorted by key; kernel-side
   `lut_lookup(keys_buf, vals_buf, n, key)` does an O(log n) binary search. Best for sparse keys
   (style/class ids, glyph codepoints).
2. **Open-addressing hash.** Upload a power-of-two `[slot: (key,val)]` table; kernel probes
   `hash(key) & mask` linearly. Best for dense-ish keys with a known load factor.
3. **Dense direct-index LUT** (the trivial case, already implied by the atlas comment): key *is* the
   array index (e.g. 8-bit palette index → ARGB). O(1), no search. Best for palettes ≤256 and
   contiguous glyph ranges.

Which lookup use cases fit (all read-only per frame → all fit the upload-only path):
- **Color / palette LUT** — indexed-color fill: kernel reads an 8-bit index framebuffer, looks up
  ARGB from a 256-entry palette buffer. Trivial dense LUT (shape 3). **Strongest first pilot** — no
  search, tiny table, obvious parity oracle (CPU does the identical array index).
- **Glyph bitmap index** — a device glyph atlas + a codepoint→atlas-offset table (shape 1 or 3). This
  is exactly what `backend_intel_kernels.spl:132` envisions and would move `draw_text` (today CPU
  only, ~547 µs/char) onto the GPU lane. Larger scope (atlas upload + AA).
- **Style / class table for GPU-composited UI** — codepoint/class-id → style struct (shape 1 binary
  search). Speculative until a GPU-composited UI path consumes it; ASSUMPTION that the web GPU-paint
  fold-in (design §8) is the eventual consumer.

Feasibility on the deployed binary: the MSL kernels are dispatched as **text literals** through the
existing session machinery (`backend_metal_msl.spl` returns one MSL string; the session compiles and
dispatches it). Adding a lookup kernel + binding one more upload buffer stays entirely inside that
machinery. **CUDA/Vulkan** have the same shape (their kernel sources are likewise embedded strings +
buffer binds) but were not byte-verified here — ASSUMPTION that the buffer-bind path generalizes;
the pilot should target Metal (the verified, preferred lane) first.

---

## 3. Selection mechanisms available

Three distinct seams exist, at three different granularities. They are complementary, not
competing.

### (a) `variants/` module-variant overlay — whole-module swap, BUILD-TARGET bound

- Manifest `variants/__init__.spl`: group `ui.renderer: { values: [default, cpu, metal, vulkan,
  webgpu], select_default: default }`, in `order: [platform, hw, lib.crypto, ui.renderer]`.
- Parsed by the resolver's bootstrap-safe line reader
  (`src/compiler/99.loader/module_resolver/var_resolution.spl` `var_parse_manifest`), **not** the
  full SDN parser. `variants/` is a resolver-only root: source imports the **stable** module name
  `std.gpu.engine2d.renderer_select`; config selects the active variant, which swaps the file
  (`variants/FILE.md`).
- Canonical `default` lives in `src` (`renderer_select.spl:1-18`, full auto-detect priority order);
  overlays under `variants/ui/renderer/<value>/std/gpu/engine2d/renderer_select.spl` return a
  target-specific order (e.g. `cpu` → `["cpu_simd", "software", "cpu"]`,
  `variants/ui/renderer/cpu/.../renderer_select.spl:6-8`).
- **Binding: per build target, whole-module.** `default`/`auto` builds never load overlays; they
  fall to runtime host detection in the base seam (`variants/FILE.md`, `renderer_select.spl:12-14`).
  `src_is_default: true`, `cache_includes_var_fingerprint: true` (`__init__.spl:28-29`). It swaps a
  *priority order*, not an op algorithm.
- **Fit:** whole-lane build products (a "cpu-only build" vs a "metal build"). Coarse; not per-op,
  not per-env at runtime.

### (b) Backend dispatch — whole-backend, RUNTIME-selected

- `Engine2D` picks a backend by name / priority (`engine.spl` `create_with_backend`,
  `create_with_backend_fast:156`, `probe_backend`), with the `SIMPLE_2D_BACKEND` env override
  winning at runtime (`draw_ir_multibackend_design.md` §4). `create_with_backend_fast` reaches the
  Metal no-mirror path (`backend_metal.spl:492 use_gpu_only`).
- **Fit:** selecting the whole GPU-vs-CPU backend at runtime by environment. This is the natural
  home for "which lane" when the choice is per-process, and it already reads env.

### (c) `BackendCapability.accelerated_ops` — PER-OP dispatch (the two-algorithm-set seam)

- `BackendCapability { kind, device_present, accelerated_ops: [text] }`
  (`backend_capability.spl:38-53`); `is_accelerated(op)` decides per op whether the backend's native
  kernel runs or the op falls through to the shared CPU reference (`SharedRaster`).
- This is D3 (`draw_ir_multibackend_design.md` §4) and is **already the per-op fork** between the two
  algorithm sets: an op in `accelerated_ops` runs the GPU kernel; an op not listed runs the CPU
  scalar reference. Today `accelerated_ops` is honestly empty for software/emu
  (`backend_capability.spl:63-73`) and real-GPU population is "deferred to a later phase."
- **Fit:** the finest granularity — per-op kernel-vs-loop. **This is where "declare a CPU variant and
  a GPU variant of one op" belongs.** The GPU-dict pilot registers its op here.

**Granularity choice.** Whole-module algorithm swap → (a) `variants/ui.renderer` (build) or (b)
`SIMPLE_2D_BACKEND` (runtime env). Per-op kernel-vs-loop → (c) `accelerated_ops` + `SharedRaster`
fallthrough. The design (§ companion doc) builds the dual-algorithm mechanism on **(c)** for op
selection and **(b)** for the process-level lane, and leaves **(a)** for build products.

---

## 4. Measured idiom table (the DO / DON'T contract)

Grounded in the perf plan measurements and bug records.

### CPU lane (interpreted) — DO

| Idiom | Why / evidence |
|---|---|
| One native `split()` / `substring`-free event scan | `parse_html` 27.3s→1.1s @N=3000 (~24x), linear thereafter (perf plan N1). |
| `Dict<text,i32>` insert-or-get instead of linear scan | `build_rule_buckets` dedup, WEB-2 LANDED `b65e52a9`. |
| Bulk `memset`/`memcpy` for clear/copy (once the extern bridge lands) | 50–200x for clear/readback (perf plan N5) — **currently blocked**. |
| One-call bulk marshalling (`rt_u32s_from_raw`) | per-pixel FFI read is ~1.4s @1024×768, 90s+ @Retina (`backend_metal_runtime_ops.spl:26-30`). |
| Inline channel math in tight loops (drop per-element fn dispatch) | 2D-1: ~12M interpreted dispatches removed for one blur (`7f549df2`). |

### CPU lane (interpreted) — DON'T

| Anti-idiom | Why / evidence |
|---|---|
| Per-element `while`/`for` over pixel/element counts on hot paths | scalar `clear`/`read_pixels` 830–897 ms/frame @720p (perf plan; `backend_software.spl:137-146`). |
| `[u8]` byte-array walks | measured **~10x worse** than native `split()` under the interpreter (perf plan N1; `css_bytes_helpers_dead_code_2026-07-07.md`). |
| Per-pixel / per-element FFI hops | one round-trip per pixel = minutes/frame (`backend_metal_runtime_ops.spl:32-36`). |
| Per-position `substring(pos, …)` | runtime primitive is O(offset) → quadratic (`text_substring_o_offset_parse_html_quadratic_2026-07-07.md`). |

### GPU lane — DO

| Idiom | Why / evidence |
|---|---|
| Data-parallel kernels (1 thread/pixel or /primitive) | the entire MSL roster (`backend_metal_msl.spl:21-32`). |
| Buffer-backed LUTs bound as an extra device buffer | feasible via `rt_metal_buffer_upload` with no new extern (§2). |
| Persistent sessions (create once, redraw per frame) | 176x–684x vs per-frame create/shutdown (`a7b57550`). |
| Batched one-FFI-shot-per-frame upload/download | `rt_metal_buffer_upload/_download/set_bytes` (`backend_metal_runtime_ops.spl:2-4`). |

### GPU lane — DON'T

| Anti-idiom | Why / evidence |
|---|---|
| Per-call session create/shutdown | negates the 176–684x persistent-session win (`a7b57550`). |
| CPU round-trip per element (readback inside a per-primitive loop) | perf plan Web Rank 1 (per-primitive Metal marshalling loses to CPU on small frames). |
| Silent software fallback labeled as GPU | metal readback silently falls to software (MEMORY 06-10); D3 honesty rule (`draw_ir_multibackend_design.md` §4). |

---

## 5. Failed / unverifiable anchors

- `rt_write_u32s_to_raw` is **declared** (`backend_metal_runtime_ops.spl:6`) but the runtime symbol
  is **not implemented** (crashes) — the declaration existing is not proof the path works.
- CUDA/Vulkan buffer-bind generalization for a LUT buffer: **ASSUMPTION** (only Metal's buffer path
  was byte-verified; CUDA/Vulkan kernel sources are embedded strings with analogous binds).
- "Style/class GPU-composited UI" consumer: **ASSUMPTION** — no current GPU-paint path consumes a
  style table; the web GPU-paint fold-in (design §8) is the presumed eventual consumer.
- The "~8% WM composite share" figure once cited for Metal-default gating is **not present anywhere
  in the tree** (perf plan N7 correction) — do not reuse it.
