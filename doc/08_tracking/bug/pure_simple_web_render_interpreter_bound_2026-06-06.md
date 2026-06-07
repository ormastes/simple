# Bug: pure_simple web render O(n²) — two distinct causes (one fixed)

**Date:** 2026-06-06  **Area:** `src/lib/gc_async_mut/gpu/browser_engine` (web render lane)
**Symptom:** the `pure_simple` web-render backend appears to "hang" at larger
resolutions. It is **not a crash and not a deadlock** — two independent O(n²) (in
canvas pixel count) bugs, one in each render path.

## Path A — heuristic surface (inline-style pages, corpus scenes) — FIXED

`SimpleWebHeuristicSurface.create` allocated the framebuffer with
`pixels = pixels.push(0u32)` in a `W*H` loop. Each push reassigns the array and,
without unique ownership, copies it — so buffer creation was O((W·H)²) and the
whole heuristic render O(n²).

**Fix (pure Simple, commit `9900d2de`):** `[0u32; width*height]` (O(n) array-repeat).
Verified: no-text page 320×240 **69s → 3s (~23×)**, linear scaling restored.
Bit-exact gate unchanged (`check-electron-simple-web-engine2d-bitmap-evidence.shs`,
`mismatch_count=0`) — identical output.

## Path B — layout renderer (real CSS pages, e.g. vanillastyle) — FIXED (rebuilt binary)

**Resolved 2026-06-06 by rebuilding & redeploying the release binary** (the
in-place fix was already in source; only the deployed binary was stale).
`cargo build --release -p simple-driver` + atomic deploy to
`bin/release/<triple>/simple`. Result via `bin/simple`: no-text 320×240 **67s→2s**,
vanillastyle 320×240 **192s→15s (~12.8×)**. Correctness verified: bit-exact gate
`mismatch_count=0`; `collections_spec.spl` 33/33 (reference semantics intact). The
deploy binary is a gitignored local artifact, so this is per-checkout — other
environments pick it up on their next driver rebuild (source already carries
`2d4579a0`).

### Root-cause detail

`simple_web_html_layout_renderer` paints via `fb[i] = color` writes. The
**in-place array-write optimization** (`CowEnv::get_mut`, commit `2d4579a0`,
**2026-06-03**) makes those O(1); without it every write CoW-clones the whole
framebuffer → O(n²).

**The deployed binaries are stale (pre-fix):**

| binary | built | no-text 320×240 | vanillastyle 320×240 |
|--------|-------|-----------------|----------------------|
| `bin/simple` → `bin/release/.../simple` | 2026-06-01 | 67s | — |
| `src/.../target/release/simple` | 2026-06-02 | 70s | 192s |
| `src/.../target/gui/debug/simple` | 2026-06-05 | (path A) | **23s** (8×) |

So `bin/simple` (what users run) and the headless `release` binary predate the
in-place fix and clone on every pixel write. The fresh `gui/debug` binary (which
`macos-gui-run` uses) has the fix — which is why GUI windows rendered while
headless `bin/simple` crawled.

**Fix:** rebuild & **redeploy the release binary** so `bin/simple` includes the
in-place array-write optimization (already in source). No renderer change needed.
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy`.

## Verify
- Path A: no-text page, 4× pixels ≈ 4× time (was ~16×). Done.
- Path B: after redeploy, re-time vanillastyle 320×240 via `bin/simple`; expect it
  to match the gui/debug binary (~20s, not ~190s). Keep the bit-exact gate green.
 
## Path C — per-node stylesheet rescans — FIXED 2026-06-07

`compute_styles()` received the already-extracted `Rules` list, but still called
`style_block_decls_for_node(html, nodes, i)` for every node. That helper reparsed
every `<style>` block and rematched selectors for the current node before the
same `rules.sels` loop applied the extracted rules again. Large GUI HTML with
many generated CSS rules therefore paid an avoidable O(nodes × stylesheet)
startup cost, and it duplicated cascade work.

**Fix (pure Simple):** delete the per-node rescan and apply the extracted rules
directly in `compute_styles()`. Focused smoke on a 40-rule / 40-node CSS-heavy
Simple Web render at 96x96:

| Measurement | Before | After |
|-------------|--------|-------|
| elapsed | `2207027us` | `1259842us` |
| checksum | `39575341662880` | `39575341662880` |

Unit coverage: `simple_web_renderer_spec.spl` includes
`applies extracted stylesheet rules without per-node style rescans`.
 
## Path D — recursive layout child discovery scans — FIXED 2026-06-07

`layout()` recursively walked children by scanning the full flat node arena for
`parent == i` in every block, flex, display-contents, and flex pre-pass. This was
another O(containers × nodes) startup/layout cost on generated GUI HTML with
many sibling widgets.

**Fix (pure Simple):** build `ChildLinks(first_child, next_sibling)` once after
parsing and walk those links during recursive layout. Focused smoke on a
180-sibling child-heavy page at 96x96:

| Measurement | Before | After |
|-------------|--------|-------|
| elapsed | `494990us` | `472511us` |
| checksum | `39574588256768` | `39574588256768` |

Unit coverage: `simple_web_renderer_spec.spl` includes
`renders sibling block children through precomputed layout links`.

## Path E — text Draw IR offload contract — IN PROGRESS 2026-06-07

The compatibility Simple Web pixel path still paints glyphs into a CPU `[u32]`
framebuffer, but `simple_web_layout_render_html_draw_ir()` now emits real Draw IR
`text` commands for `#text` nodes before rasterization. Each command carries the
text payload, color, parent id, clip rect, font size, line height, text advance,
glyph scale, and `font-rendering=bitmap-vector-backend-preferred`.

This does not complete bitmap/vector GPU glyph execution. It removes the
integration blocker where text existed only as CPU-painted pixels, so a native,
CUDA/HIP/Vulkan/Metal, or generated Simple GPU backend can consume text directly
without changing application code.

Unit coverage: `simple_web_renderer_spec.spl` asserts that the HTML layout Draw
IR batch contains a backend-consumable text command for `CMD`.

2026-06-07 backend-consumption update: `engine2d_draw_ir_adv_batch()` and
`engine2d_draw_ir_adv_composition()` now read each text command's `font-size`,
render text through FontRenderer-backed text blit buffers, count text commands,
and expose `font_offload_status`, `font_offload_reason`,
`font_gpu_glyph_returned`, and `font_production_ready` from
`vector_font_current_offload_evidence()`. Focused unit coverage asserts a 16px
Draw IR text command renders through Engine2D and reports the current
CPU-fallback reason with both glyph-return booleans false.

2026-06-07 text-cache update: the Draw IR executor now creates one
`TextBlitCache` per batch/composition instead of creating a fresh
`FontRenderer` per text command. It now caches full rendered text blit buffers
by text/color/background/font size, so repeated identical labels skip glyph
layout and text-buffer preparation entirely. Focused unit coverage renders two
`A` text commands and asserts `font_text_cache_hits == 1`,
`font_text_cache_misses == 1`, `font_generated_args_cache_skips == 1`, and
`vector_font_accelerator_stats().attempts == 1`.

2026-06-07 text-buffer cache index update: `TextBlitCache` now uses a hot entry
plus a fixed bucket index keyed by `(text,fg,bg,font_size)`. Adjacent repeated
labels still hit the hot entry, and non-adjacent repeats such as
`Repeat, Other, Repeat` return through the bucket index without another linear
scan of the text-buffer cache. Focused unit coverage asserts `bucket_hits == 1`,
`cache_hits == 2`, and unchanged `lookup_scan_count` after returning to
`Repeat`.

2026-06-07 glyph-cache update: `FontRenderer.GlyphCache` no longer linearly
scans the bounded glyph cache on every character. It keeps a hot glyph index for
immediate repeats and a fixed bucket index keyed by `(codepoint,font_size)` for
returning to a recently used glyph after another glyph becomes hot. `get_glyph()`
now persists cache lookup/insert mutations explicitly before returning cached
glyphs. Focused unit coverage asserts that repeated `A` lookups do not increase
`lookup_scan_count` or accelerator attempts, and that returning to `A` after
rendering `B` records one `bucket_hits` entry without another linear scan.

2026-06-07 glyph-return evidence update: the Draw IR boundary now proves the
positive glyph-return state when a backend rasterizer supplies vector glyph
pixels through the backend glyph slot contract. Focused unit coverage
injects a validated CUDA glyph and asserts `font_offload_status ==
"gpu-glyph-returned"`, `font_gpu_glyph_returned == true`, and
`font_production_ready == true`.

Remaining gap: production CUDA/HIP/Vulkan/Metal glyph raster kernels still need
to populate that glyph-return contract during real GUI execution.

2026-06-07 bitmap glyph evidence update: bitmap fallback now uses the same
backend-return shape as vector glyphs. `FontRenderer` routes bitmap fallback
through `rasterize_bitmap_accelerated()`, records bitmap accelerator stats, and
accepts validated backend-returned glyph pixels through a CUDA bitmap glyph slot
contract. Focused unit coverage injects one `A` glyph, asserts the returned
1x1 pixel mask, and verifies `cuda_hits == 1`,
`gpu_returned_glyphs == 1`, and `gpu_returned_glyph_pixels == 1`.

2026-06-07 Draw IR bitmap-return update: `engine2d_draw_ir_adv_*` now resets
and reads bitmap accelerator stats alongside vector stats, so a non-vector text
glyph rendered through bitmap fallback can surface `font_offload_status ==
"gpu-glyph-returned"`, `font_offload_reason ==
"cuda-bitmap-font-glyph-pixels-returned"`, and
`font_production_ready == true` at the main GUI Draw IR boundary. Focused unit
coverage injects a validated `~` bitmap glyph and verifies the Draw IR result.

2026-06-07 backend-priority glyph slot update: vector and bitmap returned-glyph
evidence now follows the GUI backend preference order: `METAL`, `CUDA`, `ROCM`,
`VULKAN`, `OPENCL`, then CPU fallback. Focused unit coverage proves native
vector glyph pixels win before CUDA, and ROCm/HIP bitmap glyph pixels win before
Vulkan/OpenCL.

2026-06-07 shared web-render evidence update: `common.ui.web_render_api` now has
`web_render_vector_font_native_compute_evidence()` so reports can validate the
same Metal -> CUDA -> ROCm/HIP -> Vulkan -> OpenCL order instead of only the
older CUDA/OpenCL pair. Focused unit coverage asserts Metal glyph-return reason
wins over CUDA, ROCm CPU-proof wins over Vulkan/OpenCL CPU-proof, and a Vulkan
checksum mismatch fails closed.

Remaining gap: production Metal/CUDA/HIP/Vulkan/OpenCL glyph raster kernels
still need to populate the vector and bitmap glyph-return contract during live
GUI execution instead of the test evidence slots.

2026-06-07 generated glyph args update: generated glyph raster kernels now have
one shared validated argument packer for `glyph_plan`, `dst`, `width`, `height`,
and `font_size`. Focused unit coverage proves invalid inputs fail closed before
allocation, valid arguments round-trip through the packed pointer layout, and
generated glyph provenance sees a real `args_ready` pointer. Remaining gap: live
backend launch/readback still needs to bind this packer into the production
Metal/CUDA/HIP/Vulkan/OpenCL glyph raster paths.

2026-06-07 native session glyph-args update: OpenCL, CUDA, and ROCm generated
glyph launches now use the same shared argument-layout validator before submit.
The CUDA and ROCm session contracts cover missing glyph plan, missing
destination, mismatched dimensions, and invalid font size with `invalid-args`
evidence instead of accepting any nonzero pointer. Remaining gap: the live GUI
text executor still needs to allocate real glyph plans/output buffers and route
successful backend readback into the vector/bitmap returned-glyph contract.

2026-06-07 Draw IR generated-args update: `engine2d_draw_ir_adv_*` now allocates
temporary glyph-plan and destination staging buffers for GPU-routed text
commands through the shared `GeneratedGlyphRasterStaging` helper, passes the
real args pointer into vector font offload evidence, and frees the owned staging
buffers after evidence capture. Focused Draw IR and generated-args coverage asserts
`font_generated_args_ready == true` and `font_generated_args_reason == "ready"`
when GPU routing is enabled, while `font_gpu_glyph_returned` and
`font_production_ready` remain false until a backend returns glyph pixels.

2026-06-07 bitmap returned-glyph slot update: bitmap backend-return probes now
scan slots `0..7`, matching vector glyph probes. This lets a backend provide
multiple bitmap glyphs for one text batch instead of only returning the first
slot. Focused font renderer coverage proves OpenCL can return a matching bitmap
glyph from slot 1 after slot 0 contains a different codepoint, with exactly one
returned glyph and pixel counted.

2026-06-07 OpenCL generated glyph backend handoff update: the OpenCL facade now
exports `simple_2d_glyph_raster_u32` in its generated 2D source and exposes a
backend-owned generated glyph smoke evidence path. The path allocates device
`glyph_plan` and `dst` buffers, packs those device handles with the shared glyph
argument layout, launches through `OpenClSession.launch_generated_2d_evidence`,
and requires typed readback evidence before reporting
`device_glyph_returned=true`. It deliberately leaves `production_ready=false`
until live vector/bitmap glyph-plan data is wired into the returned-glyph
contract.

2026-06-07 Draw IR backend-glyph evidence bridge update: `Engine2D` now keeps
the selected OpenCL backend reachable for generated glyph evidence and
`engine2d_draw_ir_adv_*` reports `font_backend_glyph_status`,
`font_backend_glyph_reason`, and `font_backend_glyph_readback` separately from
`font_gpu_glyph_returned`. This lets Draw IR surface backend handoff/readback
state without claiming production font readiness from the OpenCL smoke path.

2026-06-07 OpenCL bitmap glyph plan update: `simple_2d_glyph_raster_u32` now
reads 8x16 bitmap row data from `glyph_plan`, and
`OpenClBackend.launch_bitmap_glyph_raster_evidence()` prepares that plan from
the existing `rt_gui_get_glyph_8x16()` fallback rows. `Engine2D` exposes this as
`bitmap_glyph_raster_evidence()`.

2026-06-07 OpenCL bitmap glyph readback pixels update: successful OpenCL bitmap
glyph readback now converts the device `u32` output into grayscale glyph pixels
on `OpenClGeneratedGlyphRasterEvidence` and marks only the real bitmap path as
production-eligible.

2026-06-07 Draw IR bitmap glyph seed update: `TextBlitCache` can seed validated
backend glyph pixels into its `FontRenderer` cache, and Draw IR uses
`Engine2D.bitmap_glyph_raster_evidence()` to seed production-ready single-glyph
OpenCL bitmap readback before rendering the text payload. Remaining gap:
multi-glyph backend readback batching still needs direct returned-glyph routing.

2026-06-07 backend glyph probe cache update: `FontRenderer` now exposes a
cached-glyph query through `TextBlitCache`, and Draw IR checks it before
launching single-glyph backend bitmap evidence. Repeated labels that already
cached the glyph/font-size therefore skip duplicate backend probe/readback work
and avoid clearing rendered text payload cache entries again. Focused helper
coverage asserts seeded glyphs are visible through the cache query.

2026-06-07 font returned-glyph priority cleanup: vector and bitmap returned
glyph probes now share one native/generated font backend order helper
(`METAL`, `CUDA`, `ROCM`, `VULKAN`, `OPENCL`) before CPU fallback. This removes
duplicated CUDA/OpenCL-era branching from the production `CachedGlyph` return
contract while preserving the existing app-facing renderer behavior.

## Path F — repeated ancestor clip walks during paint — FIXED 2026-06-07

`paint()` called `ancestor_clip()` in the background, absolute, positive z-index,
image, icon, and text passes. Each call walked the node's parent chain, so deep
overflow-hidden GUI trees paid repeated O(depth) clip work per painted node and
per pass.

**Fix (pure Simple):** build a `[ClipRect]` cache once per `paint()` call using
the already ordered node array, then index `clips[i]` from each paint pass.
Focused smoke on a 48-deep overflow-hidden Simple Web render at 96x96:

| Measurement | Before | After |
|-------------|--------|-------|
| elapsed | `974687us` | `867759us` |
| checksum | `39575014374045` | `39575014374045` |

Unit coverage: `simple_web_renderer_spec.spl` already includes
`matches Chrome overflow hidden clipping for a text-free CSS matrix`.

## Path G — selector split/normalization on common simple selectors — FIXED 2026-06-07

`selector_matches_node()` split selector groups on every node/rule match, and
`selector_group_matches_node()` normalized child combinators even when a selector
had no comma, no `>`, and no descendant combinator. Class selectors also split
the desired class string on `.` even for the common single-class case.

**Fix (pure Simple):** add fast paths for single selector groups, simple selector
groups, and single-class matches before falling back to the full parser. Focused
smoke on an 80-rule / 80-node class-selector Simple Web render at 96x96:

| Measurement | Before | After |
|-------------|--------|-------|
| elapsed | `2361955us` | `2184205us` |
| checksum | `39575341662880` | `39575341662880` |

Unit coverage: `simple_web_renderer_spec.spl` includes direct child,
descendant, class, and CSS matrix cases that exercise the fallback and fast
paths.

2026-06-07 single-class reject update: `class_has()` now returns immediately
for non-matching one-token class attributes instead of constructing padded
strings and splitting the class list for every missed `.class` rule. Focused
coverage asserts `.button` does not prefix-match `class='button-primary'`.
Compound class selectors such as `.button.primary` also fail fast for a
one-token node class before splitting the selector requirement list.

## Path H — single-declaration CSS blocks paid full declaration lookup — FIXED 2026-06-07

`apply_decls()` scanned and split a declaration block once for every supported
CSS property lookup. Common Simple Web rules such as `.item{color:#123456;}`
therefore paid the whole style parser path even though the block contained one
property.

**Fix (pure Simple):** detect one-property declaration blocks, apply common
properties directly, and fall back to the existing full parser for multi-property
or unsupported blocks. Focused smoke on an 80-rule / 80-node single-declaration
Simple Web render at 96x96:

| Measurement | Before | After |
|-------------|--------|-------|
| elapsed | `1783387us` | `1687064us` |
| checksum | `182357384819455458` | `182357384819455458` |

Unit coverage remains the existing Simple Web renderer CSS matrix, plus the
focused benchmark checksum above for fast-path parity.

## Follow-up: GUI profile throughput evidence

2026-06-06 GUI profile smoke:

```sh
REPORT_PATH=doc/09_report/gui_perf_benchmark_2026-06-06.md \
  tools/gui_perf_bench/run_all_benchmarks.shs --width 320 --height 240 --frames 1
```

Initial result: the profile harness and report contract passed, but the
`simple_web_software` row was backend availability evidence only. It emitted
zero frame samples (`sample_count: 0`, `p50_frame_us: 0`, `p95_frame_us: 0`).

Resolved later on 2026-06-06 for the software render-loop profile row:

- `backend_measurement_export.spl --measure-software-render-loop true` now
  measures actual `simple_web_render_html_to_pixels_with_engine2d_backend`
  calls and emits non-zero `p50_frame_us` / `p95_frame_us`, checksum, and
  `nonzero_pixels` proof.
- The GUI profile harness initially used that broad mode for
  `simple_web_software`; the current harness uses the narrower
  `backend_measurement_software_export.spl` entrypoint.
- `simple_web_layout_render_html_pixels` now returns the painted software
  framebuffer directly for `software`/`cpu` instead of blitting it into an
  Engine2D software backend, presenting, and reading it back again.
- `backend_measurement_software_export.spl` provides a narrow software-only
  profile entrypoint, so the Simple Web software row does not import the full
  backend matrix just to measure a software render loop.
- Measured smoke at 320x240, 1 timed frame:
  - before software render-loop mode: zero frame samples, availability only;
  - after adding render-loop mode before bypass: `p95_frame_us` about
    `13,981,066`;
  - after bypassing redundant software present/readback and using the narrow
    software profile entrypoint: `p95_frame_us` about `3,011,155` on the latest
    linked smoke run;
  - checksum stayed `sum32:328820832230016`, proof stayed
    `nonzero_pixels:76800`.
- `test/03_system/gui/wm_compare/famous_site_engine2d_backend_spec.spl` now
  includes a direct layout-renderer assertion that `software` and `cpu`
  backends return identical pixels for representative corpus pages.

Follow-up text-path profiling on the same 320x240 renderer fixture:

- solid heuristic page: about `2,013us`;
- layout without text: about `244,408us`;
- layout with text before text cleanup: about `1,557,688us`;
- layout with text after char-code glyph lookup, no line substring for normal
  text, and packed glyph rows: about `1,214,473us` to `1,286,654us`, checksum
  unchanged at `328820832230016`.

The canonical GUI profile is still dominated by text/layout interpreter cost.
Further work should target bitmap/vector font rendering through the generated
Engine2D GPU text-blit lane or a compiled-mode text raster path, not another
software present/readback cycle.

## Path I — wrapped text paint allocated a substring per line — FIXED 2026-06-07

The Simple Web software text pass still built `txt.substring(off, endc)` for
every wrapped line before drawing glyphs. The glyph painter only needs the
source text and the start/end offsets, so this paid repeated text allocation in
the hottest remaining CPU-scalar path.

**Fix (pure Simple):** add range-based sparse and clipped scaled text painters
and draw wrapped lines directly from `(text, start, end)` without changing glyph
lookup, clipping, advance, or pixel output. Focused 128x96 / 3-frame software
render-loop evidence:

| Measurement | Before | After |
|-------------|--------|-------|
| `simple_web_software` p50 | `128235us` | `122665us` |
| `simple_web_software` p95 | `128897us` | `125299us` |
| checksum | `sum32:52601568094128` | `sum32:52601568094128` |

Unit coverage: `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
passed 57 scenarios after the change.

## 2026-06-06 Current Profile Evidence

The GUI profile harness now measures the Simple web software row through a real
render loop instead of an initialized-backend availability row:

- `tools/gui_perf_bench/run_all_benchmarks.shs` selects `bin/simple`,
  `bin/release/simple`, or `bin/bootstrap/simple`, in that order.
- `simple_web_software` calls
  `backend_measurement_software_export.spl --software-render-backend software`.
- `pure_simple_cuda` passes `--measure-cuda-device-buffer true`, so it records
  the actual CUDA device-buffer row instead of falling back to the generic
  backend matrix.
- Regenerated report:
  `doc/09_report/gui_perf_benchmark_2026-06-06.md`, 320x240, 1 frame,
  `profile_report_contract=true`.

Current report evidence on host `dl`:

| Lane | p50 | p95 | Proof |
|------|-----|-----|-------|
| CUDA fill | 479us | 479us | `sum32:328570011648000`, `nonzero_pixels:76800` |
| Simple web software | 3011155us | 3011155us | `sum32:328745677397784`, `nonzero_pixels:76800` |

This confirms the generated CUDA fill lane is fast and measurable, while the
pure Simple web software lane is still dominated by interpreted text/layout
work.

Open JIT blocker: running the narrow software render-loop command still prints
`[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
Unknown type: any`. A behavior-preserving local rename in
`simple_web_html_layout_renderer.parse_int` avoided a reserved-looking local
named `any`, but the fallback remains. A targeted source search found no
remaining `: any` type annotations in the immediate render path, so the next
pass should inspect the JIT lowerer/import graph and the higher-layer
`gc_async_mut` warnings emitted by this command.

## 2026-06-07 Measurement-Agent Snapshot

Measurement-only rerun on parent revision
`3d2cc6df8549cc9c57bbd4ad468540fb1e8b90a3` used the current benchmark wrapper:

```sh
REPORT_PATH=build/gui_perf_bench/measurement_agent_128x96_3_2026-06-07.md \
BUILD_DIR=build/gui_perf_bench/measurement_agent_128x96_3 \
SKIP_PROFILE_REPORT_CONTRACT=1 \
tools/gui_perf_bench/run_all_benchmarks.shs --width 128 --height 96 --frames 3
```

Current 128x96 / 3-frame evidence on host `dl`:

| Lane | p50 | p95 | Proof |
|------|-----|-----|-------|
| CUDA generated fill | `527us` | `527us` | `sum32:52571201863680`, `nonzero_pixels:12288` |
| Simple web software text | `126466us` | `133121us` | `sum32:52601568094128`, `nonzero_pixels:12288` |

Focused correctness/evidence specs passed:

- Simple Web renderer check: 2 files.
- Simple Web renderer spec: 57 scenarios.
- Draw IR advanced spec: 8 scenarios.
- Helper text spec at `test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl`: 2 scenarios.
- Font renderer spec at `test/01_unit/lib/common/text_layout/font_renderer_spec.spl`: 19 scenarios.
- Backend probe perf spec: 17 scenarios.

Remaining measured bottleneck: the Simple Web text row still reports
`runtime_execution_path="engine2d-cpu_scalar"` and `operation_family="text_blit"`.
Recent selector/style and cache fast paths are covered and compatible with the
current profile, but live GUI text is still CPU-bound until the generated
bitmap/vector glyph kernels populate the returned-glyph contract in production.

Measurement caveat: this checkout's `tools/gui_perf_bench/run_all_benchmarks.shs`
does not currently emit the earlier `simple_web_auto` static-cache row, so that
claim was not revalidated through this wrapper.
