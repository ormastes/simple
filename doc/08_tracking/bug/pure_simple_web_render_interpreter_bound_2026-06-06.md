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
 | elapsed | `787368us` | `367032us` |
 | checksum | `39568413652567` | `39568413652567` |
 
 Unit coverage: `simple_web_renderer_spec.spl` now includes
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
`FontRenderer` per text command. Repeated vector glyphs in a Draw IR batch reuse
the renderer glyph cache; focused unit coverage renders two `A` text commands
and asserts `vector_font_accelerator_stats().attempts == 1`.

2026-06-07 glyph-return evidence update: the Draw IR boundary now proves the
positive glyph-return state when a backend rasterizer supplies vector glyph
pixels through the existing CUDA glyph slot contract. Focused unit coverage
injects a validated CUDA glyph and asserts `font_offload_status ==
"gpu-glyph-returned"`, `font_gpu_glyph_returned == true`, and
`font_production_ready == true`.

Remaining gap: production CUDA/HIP/Vulkan/Metal glyph raster kernels still need
to populate that glyph-return contract during real GUI execution. Bitmap glyph
execution also still needs equivalent backend-return evidence instead of CPU
glyph preparation.
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
