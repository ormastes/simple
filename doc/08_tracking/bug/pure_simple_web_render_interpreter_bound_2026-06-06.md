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
<<<<<<< Conflict 1 of 1
%%%%%%% Changes from base to side #1
 
 ## Follow-up: GUI profile throughput evidence still incomplete
 
 2026-06-06 GUI profile smoke:
 
 ```sh
 REPORT_PATH=doc/09_report/gui_perf_benchmark_2026-06-06.md \
   tools/gui_perf_bench/run_all_benchmarks.shs --width 320 --height 240 --frames 1
 ```
 
 Result: the profile harness and report contract pass, and the `simple_web_software`
 row initializes the software backend. However `backend_measurement_export.spl`
 still emits zero frame samples (`sample_count: 0`, `p50_frame_us: 0`,
 `p95_frame_us: 0`) for Simple backend rows. Treat those rows as backend
 availability evidence only. A Simple-vs-GTK/Node throughput claim still needs
 non-zero `WmPerfCounters` phase samples or a measured render loop in the
 backend measurement path.
 
 Resolved later on 2026-06-06 for the software render-loop profile row:
 
 - `backend_measurement_export.spl --measure-software-render-loop true` now
   measures actual `simple_web_render_html_to_pixels_with_engine2d_backend`
   calls and emits non-zero `p50_frame_us` / `p95_frame_us`, checksum, and
   `nonzero_pixels` proof.
 - The GUI profile harness now uses that mode for `simple_web_software`.
 - `simple_web_layout_render_html_pixels` now returns the painted software
   framebuffer directly for `software`/`cpu` instead of blitting it into an
   Engine2D software backend, presenting, and reading it back again.
 - Measured smoke at 320x240, 1 timed frame:
   - before software render-loop mode: zero frame samples, availability only;
   - after adding render-loop mode before bypass: `p95_frame_us` about
     `13,981,066`;
   - after bypassing redundant software present/readback: `p95_frame_us` about
-    `3,291,649`;
+    `3,266,908` to `3,319,642` on repeated smoke runs;
   - checksum stayed `sum32:328820832230016`, proof stayed
     `nonzero_pixels:76800`.
+- `test/03_system/gui/wm_compare/famous_site_engine2d_backend_spec.spl` now
+  includes a direct layout-renderer assertion that `software` and `cpu`
+  backends return identical pixels for representative corpus pages.
+
+Follow-up text-path profiling on the same 320x240 renderer fixture:
+
+- solid heuristic page: about `2,013us`;
+- layout without text: about `244,408us`;
+- layout with text before text cleanup: about `1,557,688us`;
+- layout with text after char-code glyph lookup, no line substring for normal
+  text, and packed glyph rows: about `1,214,473us` to `1,286,654us`, checksum
+  unchanged at `328820832230016`.
+
+The canonical GUI profile is still dominated by text/layout interpreter cost.
+Further work should target bitmap/vector font rendering through the generated
+Engine2D GPU text-blit lane or a compiled-mode text raster path, not another
+software present/readback cycle.
+++++++ Contents of side #2
>>>>>>> Conflict 1 of 1 ends
