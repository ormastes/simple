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

## 2026-06-11 Renderer hotspot note

Current `paint(...)` still gates generated widget chrome text through
`has_nonempty_widget_text_node(nodes)`, which climbs ancestors for each
non-empty text node:

- earlier in this branch, `simple_web_renderer_spec.spl` had a passing cached
  baseline (`51 passed`);
- current uncached branch baseline has drifted to
  `simple_web_renderer_spec.spl`: `50 passed, 1 failed`
- `browser_renderer_spec.spl`: still red in the shared branch baseline
  (`75 passed, 23 failed`)
- `test/03_system/gui/wm_compare/html_compat_spec.spl`: still red in the
  shared branch baseline (`0 passed, 1 failed`)

A bounded optimization attempt replaced the repeated ancestor walk with a
precomputed widget-ancestor cache. That change was rejected in the same turn:
the main renderer spec regressed immediately under uncached execution, and the
file was restored right away. After revert, the uncached branch baseline still
stayed red at `50 passed, 1 failed`, so the current branch no longer reproduces
the older `51 passed` baseline even without the cache experiment.

Implication: this remains a valid hotspot, but there are now two separate needs:

- isolate the current uncached `simple_web_renderer_spec.spl` `50/1` failure so
  the branch baseline is stable again;
- only after that, reintroduce memoization with a behavior-exact proof path for
  the widget-text/chrome ancestor-detection contract.

## 2026-06-11 Shared text-helper metric reuse

The next safe font-path slice landed in
`src/lib/gc_async_mut/gpu/engine2d/helpers_text.spl` instead of the renderer:

- added a local `TextMetrics` helper so `glyph_height`, scale, advance, width,
  and height are derived once per call and reused by `text_buf_width`,
  `text_buf_height`, `text_render_to_buf`, and `text_blit_buffer`;
- preserved the public helper surface and pixel generation path;
- kept the optimization in Pure Simple and scoped to the shared GPU/blit text
  fallback used by non-software Engine2D backends.

Verification on the current branch:

- `helpers_text.spl` optimizer scan: `General patterns: 0`
- `test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl`: `3 passed, 0 failed`
- `test/01_unit/lib/gpu/engine2d/vector_font_offload_spec.spl`: `4 passed, 0 failed`

Branch caveat:

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl` is red on
  this branch (`1 passed, 2 failed`), but that spec exercises
  `SoftwareBackend.draw_text_bg`, which computes its own dimensions inline and
  does not call `helpers_text.spl`. Treat it as a separate baseline issue, not
  regression evidence against this shared helper change.

Follow-up landed in the same text lane:

- `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` now also uses the
  shared `text_metrics(...)` helper in both `draw_text(...)` and
  `draw_text_bg(...)`, removing another duplicated glyph-height/scale/advance
  calculation path from the software backend.

Verification after that alignment:

- Docker `simple check` on `backend_software.spl` and `helpers_text.spl`: pass
- `test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl`: still `3 passed, 0 failed`
- `test/01_unit/lib/gpu/engine2d/vector_font_offload_spec.spl`: still `4 passed, 0 failed`
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl`: still
  `1 passed, 2 failed`

Interpretation: metric derivation is now shared across GPU blit helpers and the
software text path, but the existing CPU `draw_text_bg` red spec remains a
separate branch issue. The next step in this lane should target the actual AA /
blend behavior under `SoftwareBackend.draw_text_bg`, not width/height math.

Next pass did exactly that in the software text-background path:

- added shared `text_aa_blit_buffer(...)` in
  `src/lib/gc_async_mut/gpu/engine2d/helpers_text.spl`;
- `SoftwareBackend.draw_text_bg(...)` now blits that AA payload instead of
  doing `draw_rect_filled + draw_text`;
- bilinear coverage sampling now uses floor-correct source coordinates and
  fixed-point coverage instead of binary/truncated edge math;
- the AA background payload height is padded to at least `font_size`, so the
  explicit text background box covers the full requested text cell.

Direct probe evidence on current source (`Engine2D.create_with_backend(32, 16, "cpu")`,
clear green, draw `"A"` with white-on-black background at `font_size=16`):

- outside pixel (`x=30,y=8`): stayed green (`4278255360`)
- bottom sample (`x=0,y=15`): now black/non-green (`4278190080`)
- AA scan over `16x16`: `has_intermediate=true`
- top-edge sample (`x=3,y=0`): intermediate blended color
  (`4290756543`), no longer pure fg/bg

Current branch discrepancy:

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl` still
  reports `1 passed, 2 failed` even after the direct probe matches the intended
  contract above.

The mismatch is now narrowed further:

- fresh one-case temp specs that reproduced only the first contract
  ("outside stays green and inside changes") and only the AA contract
  ("has intermediate AA") also failed under `simple test`;
- the empty-string one-case temp spec passed;
- `simple test --format json` reports the same file-level failures but does not
  currently surface per-assertion error payloads for these cases (`error: null`).

Treat this as a harness/spec discrepancy to investigate next, not as evidence
that the current `draw_text_bg` implementation is still binary. The direct
runtime probe now shows the expected AA + background behavior on the CPU path.

Root cause found in the active Rust test runner:

- `src/compiler_rust/driver/src/cli/test_runner/execution.rs`
  `build_safe_mode_child_args(...)` launches child specs as
  `simple run <raw *_spec.spl>`.
- For `draw_text_bg_spec.spl`, that raw-spec path reproduces the red result
  even when the underlying CPU rendering contract is correct:
  the child process reports
  `semantic: method to_be_true not found on type bool (receiver value: true)`.
- Running the matcher companion directly instead,
  `simple run test/.../.spipe_matchers_draw_text_bg_spec.spl`,
  passes `3 examples, 0 failures`.

Resolved in the current source lane:

- `src/compiler_rust/driver/src/cli/test_runner/execution.rs`
  `build_safe_mode_child_args(...)` now runs child specs through the existing
  `preprocess_matchers_only(path)` rewrite helper before spawning
  `simple run ...`.
- The focused Rust unit expectation was updated so
  `test_build_safe_mode_child_args_runs_spec_directly` now expects the child
  path `test/.spipe_matchers_example_spec.spl`.

Verified with a freshly rebuilt isolated binary:

- isolated rebuild:
  `CARGO_HOME=/tmp/codex-cargo-home-4 CARGO_TARGET_DIR=/tmp/codex-simple-driver-4 cargo build -p simple-driver --release`
- Docker `simple test` through that rebuilt binary:
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl`
  -> `3 passed, 0 failed`
- Docker direct matcher companion run through the rebuilt binary:
  `simple run test/.../.spipe_matchers_draw_text_bg_spec.spl`
  -> `3 examples, 0 failures`
- Regression smoke on the text-helper lane through the rebuilt binary:
  - `test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl`
    -> `3 passed, 0 failed`
  - `test/01_unit/lib/gpu/engine2d/vector_font_offload_spec.spl`
    -> `4 passed, 0 failed`

Important remaining note:

- raw `simple run test/.../draw_text_bg_spec.spl` still reproduces the matcher
  failure because the top-level `run` command itself still executes the raw spec
  path. The test-runner lane is fixed for default `simple test`; the broader
  CLI `run` parity lane remains separate follow-up work if needed.
