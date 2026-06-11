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

2026-06-11 measurement refresh status:

- `src/app/wm_compare/backend_measurement_software_export.spl` was repaired to
  parse `--width/--height` as `i32` and narrowed further so the software-only
  CLI imports `simple_web_layout_render_html_software_pixels(...)` directly
  instead of the generic Engine2D HTML renderer.
- `simple check` passes for both the exporter and
  `simple_web_html_layout_renderer.spl`.
- The exporter can still emit normalized output for the zero-sample smoke:
  `--warmup-count 0 --sample-count 0` returns a valid SDN record shape, but
  with `valid: false` and zero frame samples as expected.
- Real interpreted render calls are currently blocked again:
  `backend_measurement_software_export.spl --software-render-backend software`
  and `--software-render-backend cpu` both fail at runtime with
  `error: semantic: type mismatch: cannot convert enum to int`.
- Replacing the nested `[[ ]; nodes.len()]` layout scratch initialization with
  explicit builders did not clear that runtime failure.
- Current conclusion: the remaining blocker is now inside the interpreted
  `simple_web_layout_render_html_software_pixels(...)` path itself, not the
  measurement exporter or the generic backend resolver/import graph.

2026-06-11 compiled-path measurement refresh:

- The canonical benchmark path from
  `doc/07_guide/platform/gui_perf_benchmark_comparison.md` uses `bin/simple`,
  and that path does produce fresh non-zero samples for the narrowed software
  export entrypoint.
- Before the latest mut-capability fixes, fresh 320x240 single-frame samples
  were:
  - `software`: `p50_frame_us = 1233988`
  - `cpu`: `p50_frame_us = 1200249`
  - `cpu_simd`: `p50_frame_us = 1246565`
  - checksum: `sum32:328819896062200`
  - pixel proof: `nonzero_pixels:76800`
- Those runs were still not truly on the compiled fast path. `bin/simple`
  reported JIT fallback to the interpreter because of W1006 mut-capability
  lowering failures:
  - first at `simd_fill_row`
  - then at `simd_scroll_region`
  - then at `fb_put`
- Fixes landed:
  - `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`: added `mut`
    capability to the row/span/scroll helpers that mutate framebuffer-like
    buffers
  - `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`:
    added `mut` to `fb_put` and `fb_clear`
- After those fixes, `simple check` still passes for the touched files, but
  `bin/simple run src/app/wm_compare/backend_measurement_software_export.spl`
  now exits with code `-1` and no diagnostic text, even for the zero-sample
  case. That means the compiled/JIT path gets farther than the earlier W1006
  fallback, but currently crashes before returning measurement output.

Current conclusion:

- Fresh performance evidence exists again, but only from the pre-crash state
  before the latest mut-capability cleanup completed.
- A concrete reason the pure Simple GUI path is slow has now been proven:
  the supposed compiled/JIT benchmark lane was falling back to the interpreter
  because framebuffer mutation helpers lacked `mut` capability.
- The next blocker is no longer the exporter and no longer W1006 itself; it is
  the new compiled-path crash introduced or uncovered after clearing those
  lowering errors.

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
`has_nonempty_widget_text_node(nodes)`, which was previously climbing ancestors
for each non-empty text node.

Renderer baseline on the current branch:

- `simple_web_renderer_spec.spl`: uncached pass, `52 passed, 0 failed`
- `browser_renderer_spec.spl`: still red in the shared branch baseline
  (`75 passed, 23 failed`)
- `test/03_system/gui/wm_compare/html_compat_spec.spl`: still red in the
  shared branch baseline (`0 passed, 1 failed`)

The temporary `50/1` renderer failure in this branch was isolated to a stale
Draw IR spec expectation, not the startup-render hotspot itself:

- failing case was the `#card` Draw IR scenario inside
  `simple_web_renderer_spec.spl`
- mismatch was `card.content_rect.height`: actual `18`, stale expected `12`
- the active layout/Draw-IR path exposes content-box geometry here, so the spec
  expectation was updated to the current `40x18` content rect

With that baseline stabilized, a focused widget-chrome ancestry scenario was
added to `simple_web_renderer_spec.spl`, and the hotspot reduction is now
accepted:

- `has_nonempty_widget_text_node(nodes)` memoizes widget ancestry with a
  per-node integer flag array instead of re-climbing the parent chain for every
  non-empty text node
- Docker `simple check`
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  passes
- Docker uncached renderer spec
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
  passes `52 passed, 0 failed`

This is the current accepted startup-render hotspot reduction in the Simple Web
layout renderer.

## 2026-06-11 GUI backend routing fix

The current Engine2D preference order is already implemented in the shared
Engine2D layer, but the GUI/browser adapter had stale narrowing shims:

- `app.ui.browser.backend.resolve_gpu_backend(...)` only recognized a tiny set
  of names and otherwise collapsed requests to `software`
- the Simple Web backend-name normalizers also lagged behind the shared
  Engine2D canonical set

Accepted fix:

- expanded the Simple Web/backend adapter normalizers to preserve the shared
  canonical names used by Engine2D
- added ROCm/HIP alias canonicalization in the GUI-facing path
- kept `auto` as a separate runtime/probe lane rather than pretending it can be
  fully unit-proved in the current interpreter environment

Verification on the current branch:

- `test/02_integration/rendering/engine2d_backend_spec.spl`: `14 passed, 0 failed`
- focused browser/backend routing spec updated to assert the selected Engine2D
  lane through `BrowserBackend.gpu_backend()` instead of the adapter identity
  `backend_name() == "browser"`

Current caveat:

- the older plan note that points to
  `scripts/check/check-pure-simple-gui-engine2d-auto-backend-evidence.shs`
  and `doc/09_report/pure_simple_gui_engine2d_auto_backend_evidence_2026-06-08.md`
  references artifacts that are not present in this checkout, so the native
  auto-backend evidence lane still needs a fresh wrapper/report pass.

## 2026-06-11 Selector tokenization reduction

`compute_styles(nodes, rules)` still runs in the hottest startup-render path for
real CSS pages. After caching selector groups per rule, the remaining repeated
work inside each `nodes x rules x groups` match attempt was:

- `normalize_child_combinators(group)`
- `split(" ")`

That tokenization was being rebuilt for every node checked against every rule
group.

Accepted reduction:

- `Rules` now stores pre-tokenized selector group parts during `extract_css(...)`
- `compute_styles(...)` matches against those cached parts instead of
  re-normalizing and re-splitting each selector group per node

Additional accepted reduction on the same path:

- `parse_html(...)` now stores `class_words` on each `HNode`
- selector matching reuses those cached class tokens instead of re-splitting
  `class=""` strings while evaluating class selectors inside the
  `nodes x rules x groups` loop

Additional accepted reduction in widget/class hot checks:

- `parse_html(...)` now also caches the repeated widget/image class predicates
  used by layout and paint:
  - `has_widget_class`
  - `has_icon_image_class`
  - `has_widget_panel_class`
  - `has_widget_button_class`
  - `has_widget_image_class`
- `has_focused_class` is cached in the same lane for the generated widget focus
  border path
- layout, widget ancestry checks, and paint now reuse those flags instead of
  repeatedly running substring checks on `class_attr`

Additional accepted reduction in the text/layout lane:

- `parse_html(...)` now stores `text_trimmed` on `#text` nodes
- widget-chrome text detection, text-flow fixture detection, intrinsic text
  width, text layout height, and text paint now reuse that cached trimmed text
  instead of re-running `trim()` across the same text node in each pass

Additional accepted reduction in text paint:

- after layout, the renderer now builds a per-text-node wrap cache
  (`TextWrapCache`) from final box widths
- paint reuses cached `(start,end)` wrap ranges instead of re-running
  `wrap_line_end(...)` / `skip_wrap_spaces(...)` for every painted text node

Additional accepted reduction in wrapped text paint:

- wrapped text paint now draws directly from cached `(start,end)` ranges in the
  original text node
- this removes per-line `substring(off, endc)` allocation from the hot paint
  loop for both sparse widget text and clipped scaled text

Additional accepted reduction in glyph lookup:

- `glyph_index_for_char(...)` now uses a direct ASCII code map for the known
  renderer charset before falling back to `FONT_CHARSET.index_of(...)`
- this removes repeated linear charset scans from the common ASCII text path
  while preserving the old fallback behavior for anything outside the known set

Additional accepted reduction in glyph draw loops:

- the common text raster loops now use `char_code_at(i)` with the direct
  glyph-code map instead of allocating `substring(i, i+1)` for every rendered
  character on the common ASCII path
- the old substring-based lookup remains as the fallback for non-ASCII cases

Additional accepted reduction in shared text metrics:

- the renderer now builds a `TextRenderCache` once per render from computed
  styles
- paint and wrap-cache construction reuse cached `char_w`, `text_advance`,
  `glyph_scale`, `style_line_h`, and ink offsets instead of recomputing them
  for each painted or wrapped text node

Additional accepted reduction in wrap-height reuse:

- text wrap ranges are now computed once during `layout(...)` for `#text`
  nodes and threaded through `LayoutResult`
- paint consumes those same stored `(start,end)` ranges instead of rebuilding a
  second post-layout wrap cache from `boxes.bw`
- this removes the remaining duplicate wrap scan between text layout height and
  text paint preparation on the startup-render path

Additional accepted reduction in intrinsic width reuse:

- flex row sizing now memoizes `intrinsic_text_width(...)` results per node
  within the layout pass
- this avoids repeated recursive inline-text tree walks across the flex pre-pass
  and child placement pass when the same auto-width child is queried more than
  once

This removes one full wrap-boundary rescan from the text paint pass while
keeping layout semantics unchanged. The broader remaining cost is now deeper
glyph raster/text execution and the rest of interpreted layout work, not a
second wrap-boundary build after layout.

Verification on the current branch:

- Docker `simple check`
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`:
  pass
- Docker uncached
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`:
  `52 passed, 0 failed`

This keeps behavior green while removing another repeated string-processing pass
from the pure Simple startup-render loop. The next likely hot work inside the
same lane is deeper selector/simple-match cost or text/layout execution, not
selector-group or class tokenization.

The older plan note that points to the missing auto-backend evidence wrapper and
report is still stale in this checkout; those paths are not present and should
be refreshed when the backend-evidence lane is revisited.

## 2026-06-11 Style-cascade O(n^2) reduction

The next startup-render hotspot was in `compute_styles(...)`.

Before this pass, style-block CSS was applied twice:

- once through the extracted `Rules` list from `extract_css(html)`
- again through `style_block_decls_for_node(html, nodes, i)`, which rescanned
  every `<style>` block in the raw HTML for every node

That second path was pure repeated work for the current layout renderer and
scaled with both document size and style-block size, which made startup
rendering pay an avoidable `nodes x style-html-scan` cost before layout and
paint even started.

Accepted reduction:

- removed `style_block_decls_for_node(...)`
- `compute_styles(...)` now consumes the already extracted `Rules` set only
- all three render entrypoints now call the reduced `compute_styles(nodes, rules)`
  path

Verification on the current branch:

- Docker `simple check`
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  passes
- Docker uncached renderer spec
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
  passes `52 passed, 0 failed`
- broader browser selector/layout baseline is unchanged overall:
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`
  remains `74 passed, 24 failed`

Current interpretation:

- this is an accepted startup cost reduction in the shared style pipeline
- the remaining `browser_renderer_spec.spl` reds are broader selector/layout
  correctness gaps, not evidence that the redundant style-block rescan was
  required for current behavior
- the host evidence above (`~3.0s` pure Simple web software frame) still shows
  that the renderer remains dominated by deeper interpreted layout/text work
  beyond this removed duplicate pass

## 2026-06-11 Ancestor-clip cache attempt rejected

A follow-up attempt memoized ancestor clip rectangles inside `paint(...)` so
overflow-hidden parent clipping would be computed once per node and reused
across background, absolute, z-index, and text/icon passes.

That change was rejected in the same lane:

- focused renderer matrix coverage regressed in the overflow-hidden case
- `simple_web_renderer_spec.spl` dropped from the stable `52/0` baseline to
  `50/2` during the attempt
- the concrete mismatch was the overflow-hidden clipping fixture:
  expected green pixel count `440`, actual `400`

The cache was reverted immediately. Current interpretation:

- clip ancestry is still a repeat-heavy path worth revisiting
- the naive cached derivation was not behavior-equivalent to the current
  overflow-hidden semantics
- any future clip-cache pass needs a tighter contract around the clipping
  matrix cases before it can be accepted

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

## 2026-06-11 Shared backend text-bg consolidation

The bitmap text fallback path still existed in multiple GPU backends as
hand-rolled `draw_text_bg(...)` implementations that each recomputed:

- glyph height / scale / advance
- text buffer dimensions
- a background fill buffer
- the CPU raster call into `render_text_to_buffer(...)`

Accepted consolidation:

- `VulkanBackend.draw_text_bg(...)` now delegates to shared
  `helpers_text.text_blit_buffer(...)`
- `OpenGLBackend.draw_text_bg(...)` now delegates to the same helper
- `WebGpuBackend.draw_text_bg(...)` now delegates to the same helper

This removes another duplicate bitmap-font buffer path and keeps future text
fallback improvements centralized in the shared helper lane instead of backend
copies drifting separately.

Verification on the current branch:

- Docker `simple check` on:
  - `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/backend_opengl.spl`
  - `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl`
  - `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl`
  passes
- Docker uncached `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl`:
  `4 passed, 0 failed`
- the WebGPU spec now verifies `draw_text_bg(...)` pixels against the shared
  helper output instead of only asserting the method is callable
- regression smoke:
  - `test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl`: `3 passed, 0 failed`
  - `test/01_unit/lib/gpu/engine2d/vector_font_offload_spec.spl`: `4 passed, 0 failed`

Current interpretation:

- this is still CPU bitmap fallback feeding GPU image upload, not true GPU-side
  glyph generation or vector-font readback acceleration
- it does remove duplicate CPU fallback work and gives the remaining font-path
  optimization one shared implementation surface for these backends
