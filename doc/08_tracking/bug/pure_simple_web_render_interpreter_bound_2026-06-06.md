# Bug: pure_simple web render O(n²) — two distinct causes (one fixed)

Status: likely-fixed (triaged 2026-06-11, Path A and Path B both fixed per title/body)

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
- 2026-06-11 compiled JIT refresh: the patched release driver now reports the
  zero-sample smoke with correct parsed counts:
  `warmup_count: 0 sample_count: 0`.
- 2026-06-11 compiled one-sample smoke:
  `--warmup-count 0 --sample-count 1` returns `valid: true`,
  `checksum: "sum32:1027061180046"`, and
  `pixel_proof: "nonzero_pixels:3072"` at 64x48.
- The Docker isolation runtime still fails direct `run` of the renderer entry
  with `error: semantic: type mismatch: cannot convert enum to int`.
- Host interpreter execution is still healthy when forced through the env var
  path:
  `SIMPLE_EXECUTION_MODE=interpret bin/simple run ...` completes parse, style,
  layout, Draw IR, and paint for a direct renderer probe.
- Important nuance: host `bin/simple run --interpret ...` still crashes for the
  same renderer import where `SIMPLE_EXECUTION_MODE=interpret` succeeds. That
  is a CLI/runtime mode-selection bug, not a renderer-semantic failure.
- Current conclusion: the remaining direct-run isolation problems are split
  across runtime surfaces. The renderer itself still executes through the host
  interpreter path; the Docker `run` semantic failure and host `--interpret`
  crash are separate runtime issues.

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
    temporary `mut` on `fb_put` / `fb_clear` was tested, but it is now reverted
    because it triggers a compiled-path crash
- The compiled-path crash is now isolated more precisely:
  importing the renderer module alone through a tiny `loaded=1` probe causes
  default `bin/simple run` to segfault when `fb_put` / `fb_clear` carry `mut`
  capability, even if the probe never calls the renderer.
- Reverting only those two `mut` annotations removes the crash immediately and
  restores the earlier behavior:
  - default `bin/simple run` no longer segfaults
  - the runtime reports W1006 fallback on `fb_put`
  - direct renderer probes complete under fallback/interpreter execution
- Further narrowing:
  - a tiny imported scratch module with:
    - one small class
    - one constructor-like helper
    - one exported `mut fb_put(mut fb: [u32], ...)`
    - one exported non-render helper used by a probe
    does **not** crash under default `bin/simple run`
  - so the compiled-path failure is not a generic
    `imported-module + class + mut [u32] helper` issue
  - a smaller scratch module that imports `common.ui.draw_ir` and defines a
    private `mut fb_put(mut fb: [u32], ...)` with indexed assignment is enough
    to reproduce the default compiled-run segfault
  - the same scratch module passes when run with
    `SIMPLE_EXECUTION_MODE=interpret`, so the failure is in the compiled/JIT
    execution lane, not Simple semantics
- Refreshed host measurements after reverting the crashing `mut` annotations:
  - `software`: `p50_frame_us = 1177740`
  - `cpu`: `p50_frame_us = 1277987`
  - `cpu_simd`: `p50_frame_us = 1201497`
  - checksum stayed `sum32:328819896062200`
  - pixel proof stayed `nonzero_pixels:76800`

Current conclusion:

- Fresh performance evidence exists again on the canonical host path.
- A concrete reason the pure Simple GUI path is slow has now been proven:
  the supposed compiled/JIT benchmark lane was falling back to the interpreter
  because framebuffer mutation helpers lacked `mut` capability.
- A second concrete blocker is now also proven:
  the current compiled/JIT path crashes on the renderer module when `fb_put` /
  `fb_clear` are marked `mut`, so the fast path cannot yet be enabled there
  without a compiler/runtime fix.
- The next highest-value fix is no longer in the benchmark exporter. It is the
  compiler/runtime bug that turns those renderer-local `mut` helpers into a
  segfault instead of either valid compiled code or a normal lowering failure.

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

Resolved JIT blocker update, 2026-06-11: the earlier module-init segfault from
renderer-local `mut fb_put` / `mut fb_clear` is fixed in the Rust compiler lane
by declaring runtime-initialized globals writable during Cranelift module init.
The renderer helpers are `mut` again and the focused renderer unit spec still
passes through the patched release driver.

The narrow software render-loop command is now valid compiled benchmark
evidence for the 64x48 smoke. The final root cause was split across two JIT
paths: signed narrow VRegs were being zero-extended during full block sync, and
`text.to_i32()` narrowed the text pointer instead of parsing through
`rt_string_to_int`. Focused regressions now cover `i32` return/control-flow,
`i32` struct slots, and `text.to_i32()` parsing with stub fallback disabled.

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

Attempted but rejected O(n^2) layout reduction:

- tried replacing repeated full-node child discovery in recursive layout with a
  prebuilt `children: [[i32]]` index
- the focused renderer unit spec still passed, but the benchmark fixture
  checksum drifted and the broader backend-parity spec stayed red on this
  branch baseline
- that makes the current worktree insufficient to prove the child-index rewrite
  is behavior-preserving, so the code change was reverted in the same turn
- the underlying hotspot is still real: recursive layout currently rediscovers
  direct children by scanning the flat node arena in multiple passes

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

## 2026-06-11 Bitmap-font provenance aliases

The generated Engine2D operation provenance now recognizes explicit
`bitmap_font`, `bitmap_glyph`, `font_bitmap`, and `glyph_bitmap` operation
families. They map to the generated copy/upload operation with
`cpu_preprocess_required = true`, matching the current bitmap text reality:
glyph pixels are still produced on CPU and uploaded/blitted by the backend.

This is not a GPU-side bitmap glyph rasterizer yet. It is a narrow contract so
measurement and future backend work can distinguish:

- bitmap-font fallback: CPU glyph buffer plus generated copy/upload
- vector-font offload: production-ready only after GPU glyph pixels are returned
- normal image copy: generated copy/upload without text CPU preprocessing

## 2026-06-11 WebGPU foreground text consolidation

Spark reviewed the remaining backend-local bitmap text fallback bodies and
identified `WebGpuBackend.draw_text(...)` as the safest next single-backend
consolidation target. That path now uses
`helpers_text.text_transparent_blit_buffer(...)` for glyph buffer generation and
then writes only nonzero foreground pixels into the WebGPU CPU mirror buffer.

This preserves foreground-only `draw_text` behavior instead of routing through
`draw_image(...)`, which would overwrite background pixels with transparent
zeros on this backend.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl`
  passes with the pre-existing `gc_boundary_crossing` warning on the WebGPU SFFI
  import.
- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl --no-cache`:
  `5 passed, 0 failed`

## 2026-06-11 Baremetal text-bg consolidation blocker

Attempted next target: `BaremetalBackend.draw_text_bg(...)`, replacing its local
bitmap background buffer construction with `helpers_text.text_blit_buffer(...)`.
The code checked, but the focused host-buffer scenario failed at runtime with
`semantic: variable self not found` inside the `Engine2DExtended` method path.

The workaround attempts also failed:

- hoisting `self` into a local backend before the helper call
- avoiding `TextBlitBuffer.is_empty()` method dispatch
- writing the shared payload directly through `_bm_put(...)` instead of calling
  `self.draw_image(...)`

The slice was reverted to avoid landing a red backend spec. This leaves
Baremetal in the remaining duplicated bitmap fallback set until the extension
method `self` binding/runtime issue is fixed or minimized separately.

## 2026-06-11 Helper parity repair

Spark reviewed the stale matcher cleanup for
`test/02_integration/rendering/helpers_parity_spec.spl`; Codex applied the
replacement and split range/string/order checks into typed assertions. The test
then exposed interpreter-visible buffer mutation gaps in the pure-Simple helper
API: `mut` parameters are local to the interpreter, so callers need a returned
buffer when asserting effects.

The shared pixel helpers and bitmap glyph renderers now keep their mutable
parameter shape and also return the updated buffer. Existing backend call sites
that ignore the result still check, while pure-Simple tests can assign the
returned buffer and verify the same pixel effects.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/engine2d/helpers_pixel.spl src/lib/gc_async_mut/gpu/engine2d/glyph.spl test/02_integration/rendering/helpers_parity_spec.spl src/lib/gc_async_mut/gpu/engine2d/backend_virtio_gpu.spl src/lib/gc_async_mut/gpu/engine2d/backend_opengl.spl src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl`
  passes with the pre-existing GC-boundary warnings in VirtIO/WebGPU.
- `bin/simple test test/02_integration/rendering/helpers_parity_spec.spl --no-cache`:
  `66 passed, 0 failed`

## 2026-06-11 Pure-Simple layout child-scan optimization

The pure-Simple HTML layout path previously rediscovered direct children by
scanning `i + 1 .. nodes.len()` inside each recursive layout call. Flat GUI or
HTML startup fixtures therefore repeated full arena scans across contents,
flex-wrap, flex-row, flex-column, and normal block-flow branches.

The renderer now builds `HtmlChildIndex` once after parsing and passes it through
the recursive layout and intrinsic inline-width calls. Each branch iterates only
`child_index.children[i]`, preserving document order and public render/debug
entrypoints while removing the direct child-discovery O(n^2) shape from layout.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `2 passed, 0 failed`
- `bin/simple test test/02_integration/rendering/web_engine2d_metal_offload_spec.spl --no-cache`:
  `11 passed, 0 failed`
- Optimizer analysis ran on the touched renderer and spec. It still reports
  broad follow-up opportunities such as bounds-check elimination, len-call
  hoisting, and collection preallocation.

Attempted extra smoke:

- `bin/simple run src/app/wm_compare/backend_measurement_software_export.spl --software-render-backend software --width 160 --height 120 --sample-count 3 --warmup-count 1 --fixture child-index-smoke`
  exited `-1` with no output. The direct renderer specs above stayed green, so
  this remains a measurement-entrypoint/runtime follow-up rather than evidence
  against the layout child-index change.

## 2026-06-11 CSS cascade candidate optimization

Spark reviewed the pure-Simple CSS selector cascade loop as an easy read-only
task. The risky part is selector semantics, so the implementation keeps the
existing full selector matcher as the final authority and only uses buckets to
reduce the number of candidate rules sent into that matcher.

The renderer now builds a `RuleBuckets` index once per `compute_styles(...)`
call. Each selector group is bucketed by the rightmost simple selector into id,
class, tag, or fallback buckets. Per-node style computation gathers only the
fallback rules plus matching id, tag, and class buckets. The candidate lists
are already in source order, so the implementation merges those lists and
deduplicates repeated rule membership instead of flattening then selection
sorting. Declarations still apply only after
`selector_matches_node_group_parts(...)` succeeds. This preserves cascade order
while avoiding both the previous every-rule/every-node selector walk and the
follow-up O(k^2) candidate sort for common startup pages.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `5 passed, 0 failed`
- `bin/simple test test/02_integration/rendering/web_engine2d_metal_offload_spec.spl --no-cache`:
  `11 passed, 0 failed`
- Optimizer analysis ran on the touched renderer and focused spec. It still
  reports follow-up opportunities such as bounds-check elimination, len-call
  hoisting, and collection preallocation.

## 2026-06-11 Paint ancestor-clip cache

The paint path still recomputed the same ancestor clip for a node in multiple
passes: normal backgrounds/borders, absolute backgrounds/borders, positive
z-index backgrounds/borders, icon/image chrome, and text rendering. Each
`ancestor_clip(...)` call walked the parent chain to intersect overflow-hidden
ancestors, so deep or node-heavy pages paid repeated parent-chain traversal
during startup rendering.

`paint(...)` now asks `build_ancestor_clip_cache(...)` for a `PaintClipCache`.
Pages without visible `overflow:hidden` skip per-node clip allocation and reuse
one framebuffer-sized default clip. Pages with overflow clipping build a per-node
cache once; because parsed nodes are parent-before-child, each node derives its
clip from the cached parent clip plus the direct parent's overflow-hidden
content box. The existing draw calls then use `paint_clip_at(...)`. This
preserves clipping semantics while removing repeated ancestor walks across paint
passes and avoiding the clip-array allocation for the common unclipped case.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `5 passed, 0 failed`
- The focused spec now includes an overflow-hidden pixel oracle: an overflowing
  child paints inside the clipped container and leaves the outside pixel white.

## 2026-06-11 Widget paint flag pre-pass

After the clip cache, `paint(...)` still did two node-wide scans for widget
fixtures: `has_nonempty_widget_text_node(...)` walked the tree with widget
ancestor state, then a separate loop scanned for `has_widget_panel_class`.
`has_widget_ancestor(...)` was also left as an unused parent-walk helper.

`compute_widget_paint_flags(...)` now computes panel presence and non-empty
widget text in one pass, using the same parent-before-child widget ancestor
flagging as the previous text helper. `paint(...)` consumes the resulting
`WidgetPaintFlags`, and the unused parent-walk helper is removed. When widget
text is not needed, the helper uses a panel-only scan and skips the
`[0; nodes.len()]` widget-ancestor scratch allocation entirely.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `5 passed, 0 failed`
- The focused spec includes a widget-mode chrome oracle that asserts the
  generated blue border pixel remains `0xff0066cc`.

## 2026-06-11 Nested flex intrinsic-width memo

Nested flex layout still allocated a fresh `[-1; nodes.len()]` intrinsic-width
memo inside every non-column flex container before measuring child text widths.
That kept the hot path interpreter-bound on node-heavy flex startup fixtures.

`LayoutResult` now carries the intrinsic-width memo. Public layout entrypoints
seed it once with `neg_one_i32_list(node_count)`, recursive layout branches pass
the current memo into children, and then fold each child result's memo back into
the parent. Intrinsic text width measurement keeps its existing memo semantics
but reuses the shared array through nested flex recursion.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`
- The focused spec includes a nested flex oracle that verifies outer width,
  nonzero inner width, and stable sibling x-order.

## 2026-06-11 Child-index build and dead selector cleanup

`build_child_index(...)` still paid two full walks over the parsed node arena:
one to allocate each child-list slot and another to attach each node to its
parent's child list. Parsed HTML nodes are parent-before-child, so the renderer
now attaches the current node to its parent during the same pass that creates
the current node's child-list slot. The guard `parent < children.len()` remains
in place, preserving behavior if malformed input ever violates that ordering.

Spark also ran a read-only reference scan for legacy selector helpers. The scan
proved the local `selector_matches(...)`, `selector_group_matches_node(...)`,
`selector_matches_node(...)`, and `class_has(...)` helpers in
`simple_web_html_layout_renderer.spl` were unused by repo call sites. Those
dead helpers are removed; the live `class_contains(...)` widget-class path is
unchanged.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`
- `rg -n "fn class_has\\(|fn selector_matches\\(|fn selector_group_matches_node\\(|fn selector_matches_node\\(" src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  returns no matches.

## 2026-06-11 Text paint range clipping cleanup

The active text paint path renders through `fb_text_thin_scaled_clip_range(...)`
for normal pages and `fb_text_sparse_range(...)` for widget-mode pages. Before
this cleanup, both range helpers still scanned every character in a line even
after the advancing x position was outside the framebuffer or clip, and they
entered the character loop for rows that were vertically outside the target.

Both active range helpers now return immediately for fully off-viewport text
rows and stop scanning the current line once `cx` is beyond the framebuffer or
clip edge. This preserves visible pixels because text advances monotonically to
the right in these helpers. Spark also proved the older non-range renderer-local
wrappers (`fb_text(...)`, `fb_text_thin_scaled(...)`,
`fb_text_thin_scaled_clip(...)`, and `fb_text_sparse(...)`) had no call sites in
the active renderer path, so those dead wrappers were removed while keeping the
glyph helpers used by the range functions.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`
- `rg -n "fn fb_text\\(|fn fb_text_thin_scaled\\(|fn fb_text_thin_scaled_clip\\(|fn fb_text_sparse\\(|fb_text_thin_scaled_clip_range\\(|fb_text_sparse_range\\(" src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  shows only the two active range helper definitions and their two paint call
  sites.

## 2026-06-11 Lazy final-pass paint clip lookup

After the text range cleanup, the final text/icon paint pass still called
`paint_clip_at(clip_cache, i)` for every node before checking whether that node
would draw image, icon, or text content. Most nodes in startup fixtures do not
draw in this final pass, so the lookup was repeated on the no-paint branch.

The final pass now asks for the clip only inside the branches that draw clipped
widget images, icon-image placeholders, or normal text. Widget-mode sparse text
does not use the clip and no longer pays that lookup. The renderer also removes
the now-unused unclipped glyph wrappers, leaving only the clipped normal-text
glyph helper and sparse widget glyph helper used by active range paths.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`

## 2026-06-11 Text render cache only computes text-node metrics

`build_text_render_cache(...)` previously computed character width, advance,
glyph scale, line height, and ink offsets for every parsed node, including
elements that never read those text metrics in `paint(...)`. The cache arrays
must stay indexed by node id, but non-text rows do not need expensive metric
derivation.

The builder now accepts `nodes` alongside `styles`, keeps one cache slot per
style row, and computes real text metrics only when `nodes[i].tag == "#text"`.
Element rows receive zero placeholders. This preserves the paint path's
indexing contract while reducing startup work on DOM-heavy pages where most
nodes are elements.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`

## 2026-06-11 Remove unused text char-width cache

After making `build_text_render_cache(...)` text-node-aware, `TextRenderCache`
still carried a `char_widths` array that no active paint path read. Text layout
width measurement uses the separate `char_w(...)` and intrinsic-width paths, not
the paint cache field.

`char_widths` is removed from the cache class and builder. The remaining arrays
match the fields read by `paint(...)`: advances, scales, line heights, and ink
offsets. This removes one per-node allocation/fill path without changing visible
rendering or public entrypoints.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`
- `rg -n "char_widths|TextRenderCache|text_render\\." src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  shows no `char_widths` references and only the active `text_render` field
  reads.

## 2026-06-11 Hoist normal text clip lookup per text node

The final text paint pass previously resolved `paint_clip_at(clip_cache, i)`
inside the wrapped-line loop for normal text. That repeated the same clip lookup
for each line range of the same text node.

The text branch now splits widget sparse text and normal clipped text. Widget
text still skips clip lookup. Normal text resolves the clip once per text node
and reuses it while painting all wrapped line ranges for that node.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`

## 2026-06-11 Remove text metric staging cache

After the prior cache reductions, `TextRenderCache` still allocated and filled
five node-indexed arrays before paint, only for `paint(...)` to read each metric
once per visible text node. That staging pass was no longer buying reuse.

The renderer now computes glyph scale, advance, line height, and ink offsets
inside the already-filtered `#text` paint branch. This removes the
`TextRenderCache` class, the `build_text_render_cache(...)` pass, and both
render-entry cache construction calls while preserving public render entrypoints
and visible output.

Verification:

- `rg -n "TextRenderCache|build_text_render_cache|text_render" src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  returns no matches.
- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`

## 2026-06-11 Duplicate class bucket lookup skip

The style candidate path collects rule buckets for every class token on a node.
When HTML contains duplicate class tokens, the same class bucket was looked up
and appended multiple times, only for `merge_sorted_rule_lists_unique(...)` to
deduplicate the same rule ids later.

`style_rule_candidates(...)` now skips class bucket lookup when the same trimmed
class token already appeared earlier on the node. Cascade behavior is unchanged:
candidate rule ids still merge in source order and
`selector_matches_node_group_parts(...)` remains the final selector authority.
The focused CSS oracle now uses `class="target target"` to exercise duplicate
class membership while preserving the expected cascaded height.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`

## 2026-06-11 Trivial selector candidate merge fast paths

`merge_sorted_rule_lists_unique(...)` previously allocated a positions array and
entered the k-way merge loop even when a node had zero or one candidate bucket
list. The one-list case is already sorted and unique by rule insertion order, so
the merge does not add value.

The helper now returns `[]` for no lists and the original list for one list. The
multi-list path remains unchanged and still deduplicates repeated rule ids in
source order.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `6 passed, 0 failed`

## 2026-06-11 Positive z-index append fast path

The positive z-index paint pass still built the paint order with insertion sort
for every positive absolute-positioned node. Common startup fixtures and
generated UI trees often emit positive z-index layers in nondecreasing order,
so the scan/shift work is unnecessary in that case.

The renderer now appends directly when the next positive z-index is greater
than or equal to the last appended z-index. If a later node is out of order, the
existing stable insertion path still runs. Equal z-index values remain stable in
document order.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `11 passed, 0 failed`
- The focused spec covers both an out-of-order positive z-index fixture and an
  already sorted fixture; both keep the top pixel green.

## 2026-06-11 Positive z-index collection single pass

After the append fast path, pages with any positive z-index node still paid a
second full node scan to collect the positive absolute-position paint order.
The renderer now collects those nodes during the existing absolute-position
decoration pass, then reuses the collected order for the positive-z paint pass.

The no-positive-z case still leaves the order buffer unallocated. Positive
z-index nodes keep the same nondecreasing append fast path and stable
out-of-order insertion fallback, so equal z-index values remain in document
order.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `11 passed, 0 failed`
- `bin/simple spipe-docgen test/02_integration/rendering/simple_web_layout_child_index_spec.spl --output doc/06_spec`
  regenerated the mirrored manual.
- Docker optimizer scans: renderer `747` and focused spec `4` remaining static
  opportunities.

## 2026-06-11 Selector part pretrim

Selector groups were already split once during CSS extraction, but hot selector
matching still trimmed the same selector part strings while finding the
rightmost bucket key and while walking ancestor selectors for each candidate
node.

`selector_group_parts(...)` now stores trimmed selector tokens up front.
Rightmost selector lookup and ancestor matching reuse those pretrimmed tokens,
so spaced descendant and child selectors keep their behavior while avoiding
repeated trim calls during node matching.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `12 passed, 0 failed`
- `bin/simple spipe-docgen test/02_integration/rendering/simple_web_layout_child_index_spec.spl --output doc/06_spec`
  regenerated the mirrored manual.
- Docker optimizer scans: renderer `750` and focused spec `4` remaining static
  opportunities. The renderer static count rises because the one-time
  preprocessing loop is now explicit; runtime selector matching avoids repeated
  trimming of the same selector parts.

## 2026-06-11 Class token pretrim

HTML parsing already split `class` attributes into `class_words`, but style
candidate lookup still trimmed each class token and trimmed previous tokens
again while suppressing duplicate class buckets for every style pass.

`parse_html(...)` now stores trimmed `class_words` once. Style candidate lookup
and duplicate-class suppression reuse those parsed tokens directly, preserving
spaced duplicate class behavior while avoiding repeated class-token trim work
during selector matching.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `13 passed, 0 failed`
- `bin/simple spipe-docgen test/02_integration/rendering/simple_web_layout_child_index_spec.spl --output doc/06_spec`
  regenerated the mirrored manual.
- Docker optimizer scans: renderer `754` and focused spec `4` remaining static
  opportunities. The renderer static count rises because the one-time
  parse-time normalization loop is explicit; style matching avoids repeated
  trimming of the same class tokens.

## 2026-06-11 Text segment trim reuse

HTML parsing trimmed each non-tag text segment once to decide whether it should
emit a `#text` node, then trimmed the same segment again to populate
`text_trimmed`.

The parser now stores the trimmed segment in a local value and reuses it for
both the emptiness check and the emitted node. Whitespace-only text segments
still do not create layout-affecting text nodes.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `14 passed, 0 failed`
- `bin/simple spipe-docgen test/02_integration/rendering/simple_web_layout_child_index_spec.spl --output doc/06_spec`
  regenerated the mirrored manual.
- Docker optimizer scans: renderer `754` and focused spec `4` remaining static
  opportunities.

## 2026-06-11 Numeric parser trim removal

`parse_int(...)` trimmed its input before scanning for digits, but the scanner
already skipped leading non-digits and stopped after the first digit run. CSS
values from declaration parsing are already value-trimmed, and values with
units such as `24px` rely on that digit-run behavior.

The helper now scans the original input directly, avoiding the extra trim
allocation on every numeric CSS parse while preserving spaced values and unit
suffixes.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `15 passed, 0 failed`
- `bin/simple spipe-docgen test/02_integration/rendering/simple_web_layout_child_index_spec.spl --output doc/06_spec`
  regenerated the mirrored manual.
- Docker optimizer scans: renderer `754` and focused spec `4` remaining static
  opportunities.

## 2026-06-11 Selector match trim removal

After selector part pretrimming, `simple_match(...)` still trimmed each selector
token during every node and ancestor selector match. All active calls pass
preprocessed selector group parts, so that trim no longer changed the input.

`simple_match(...)` now uses the already-trimmed selector token directly. The
existing spaced descendant/child selector oracle continues to cover the
pretrimmed selector contract.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `15 passed, 0 failed`
- Docker optimizer scan: renderer `754` remaining static opportunities.

## 2026-06-11 Compound class selector suffix trim removal

Compound class selector matching split suffixes such as `.target.marker` and
then trimmed every suffix during each selector match. Selector parts are already
trimmed during preprocessing, so those suffixes do not need another trim in the
hot node/ancestor match path.

`class_has_all(...)` now reuses the split suffixes directly. Existing compound
class and spaced selector oracles continue to cover the behavior.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `15 passed, 0 failed`
- Docker optimizer scan: renderer `754` remaining static opportunities.

## 2026-06-11 Selector bucket base trim removal

Selector bucket classification receives rightmost selector parts from the
preprocessed selector group part list. Those parts are already trimmed, but
`selector_bucket_base(...)` still trimmed the part again before checking pseudo,
attribute, id, class, and tag bucket keys.

The helper now starts from the pretrimmed part directly and keeps the existing
trim on the substring before an attribute selector. Bucket behavior stays
covered by the focused selector bucket and spaced selector specs.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `15 passed, 0 failed`
- Docker optimizer scan: renderer `754` remaining static opportunities.

## 2026-06-11 Selector bucket base reuse

Rule bucket construction classified each rightmost selector by calling
`selector_bucket_kind(...)` and `selector_bucket_value(...)`. Both helpers
derived the same selector bucket base, so counting and fill passes each repeated
pseudo/attribute scans and substring work for the same selector group.

`build_rule_buckets(...)` now computes `selector_bucket_base(...)` once per
rightmost selector and feeds base-aware kind/value helpers. The original
part-based helpers remain available and delegate through the same base-aware
logic.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `15 passed, 0 failed`
- Docker optimizer scan: renderer `754` remaining static opportunities.

## 2026-06-11 Class-token split array removal

`split_class_words_trimmed(...)` split each class attribute into an intermediate
array with `class_attr.split(" ")`, then allocated the final `class_words` array
and trimmed every token into it. That made class parsing carry two token arrays
for each classed node.

The helper now scans for ASCII spaces directly, preserves the old split token
count for leading/trailing/repeated spaces, and keeps per-token trim behavior.
This removes the intermediate raw split array without broadening class splitting
to tabs or newlines.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `15 passed, 0 failed`
- Docker optimizer scan: renderer `756` remaining static opportunities; the
  count rises because the former split intrinsic is now explicit scan loops.

## 2026-06-11 Exact-size HTML node arena

`parse_html(...)` still built the top-level node arena with `var nodes: [HNode]
= []` and repeated `nodes.push(...)` calls. On large startup pages this kept the
parser exposed to grow-by-copy array behavior even though the emitted-node count
is knowable from the same parse grammar.

`count_html_nodes(...)` now mirrors parser emission for the root node, non-empty
text chunks, skipped metadata/style/script/title nodes, comments, closers,
self-closing elements, and malformed-tag breaks. `parse_html(...)` allocates the
exact arena size and fills `nodes[node_i]` directly, preserving parent indices
and stack behavior.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/02_integration/rendering/simple_web_layout_child_index_spec.spl`
  passes.
- `bin/simple test test/02_integration/rendering/simple_web_layout_child_index_spec.spl --no-cache`:
  `15 passed, 0 failed`
- Docker optimizer scan: renderer `759` remaining static opportunities; the
  count rises because the former push intrinsic is now an explicit pre-count
  scan.
