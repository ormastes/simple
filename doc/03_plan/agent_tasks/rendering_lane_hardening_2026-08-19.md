# Rendering Lane Hardening Plan (wm/gui/web/2d) — 2026-08-19

Status: Active. Phase 0 (sanitize) in progress.
Host: Linux, RTX A6000 + TITAN RTX, Vulkan 1.4 (nvidia + llvmpipe), nvcc 13.0,
Playwright Chromium available, RenderDoc binary NOT installed (install or use
external-host wrapper `check-renderdoc-external-host-capture.shs`).

## Phase 0 — Sanitize (BLOCKING, per user directive 2026-08-19)
Fix ALL existing rendering test failures first; push each fix to GitHub via
`sh scripts/check/land.shs` (never raw `jj git push`).
Suites: `test/02_integration/rendering/`, `test/system/wm_compare/`,
`test/03_system/gui/`, `test/03_system/browser_engine/`,
`test/unit/lib/common/text_layout/`, engine2d/vulkan check scripts.
Known-open: HWIR foundation spec 21 failures (`hwir_foundation_spec_residual_failures_2026-08-16.md`),
riscv gen2 qualification CLI contract mismatch (2026-08-14).

## Research summary (4 parallel agents, 2026-08-19)
- **Capture**: CDP `Page.screenshot` (play/page.spl), `wm_screenshot*`
  (play/wm/mod.spl), QEMU screendump PPM. Diff engine exists but exact-only:
  `src/app/wm_compare/backend_parity.spl:diff_buffers`; golden PPM gate
  `golden_gate.spl`. STUBS: `src/os/compositor/screenshot_compare.spl`
  `find_diff_regions` returns [] — the region-analysis gap.
- **srenderdoc** = `src/lib/common/renderdoc/backend_render_record.spl`
  (versioned record + diff) + `backend_render_receipt_wire.spl` (BRR1 codec).
  Real RenderDoc glue: `scripts/lib/renderdoc-evidence-common.shs`;
  RDC→XML parser `src/app/test/renderdoc_replay_inspect.spl`.
  Closest log compare: `scripts/check/check-linux-vulkan-render-log-compare.shs`.
- **Web engine**: `src/lib/gc_async_mut/gpu/browser_engine/` (layout/paint/css)
  + parallel `src/lib/blink/` tree (ownership unclear — needs decision).
  Chrome differential harnesses exist per stage: `tools/{web_diff,layout_diff,
  paint_diff,composite_diff,vector_font_diff}` with CONTRACT.md each.
  No per-component (counter/button/input) harness; web branch coverage
  unmeasured (5% @cover annotations only).
- **Fonts**: nogc_sync_mut/text_layout (3400 L) has ZERO unit specs; raster
  fallback chain ends in 5x7 bitmap — the known Chrome text divergence
  (text_raster_track 1292 mismatches, mdi_chromium plan).
- **xxIR = HWIR** (`src/compiler/50.mir/hwir/`). No "eager allocation" concept
  exists anywhere — must be defined+implemented for GPU draw-IR
  (`gpu/engine2d/draw_ir_*.spl`) if the goal stands.
- **GPU offload**: gpu_runnable_scan is inventory-only; no `@gpu_runnable`
  pass. CUDA & Vulkan are parallel lane backends (no interop); parity gate
  `check-processing-cuda-vulkan-native-parity.shs`. SIMD lanes via
  `check-cpu-simd-engine2d-*` + `check-llvm-simd-row-native-arch.shs`.
- **Doom**: `game2d/ports/doomgeneric.spl` is a 172-line shim; backends
  SDL+headless only — no web/gui backend.

## Phases (after sanitize)
1. **Capture-diff infra**: implement `find_diff_regions` + shift/alignment
   search (offset sweep, per-region bbox), PNG→ARGB ingestion bridging CDP
   screenshots into `diff_buffers`. Tests: unit on synthetic shifted buffers.
2. **Layout→textual debug tool**: bounds→ASCII/text-grid renderer over
   `ui_access_snapshot` + `widget_draw_ir`; diffable textual layout format for
   both chrome (CDP layout dump) and Simple. Tests with fixtures.
3. **srenderdoc↔RenderDoc compare**: adapter RDC-XML actions →
   `BackendRenderField` paths + per-drawcall alignment analysis on top of
   `BackendRenderRecordDiff`. Chrome-web vs GUI srenderdoc record compare.
   Tests with recorded fixtures.
4. **Web component parity**: add counter component fixture + per-component IO
   harness (chrome CDP vs Simple engine, per-stage reuse of tools/*_diff);
   branch-coverage gate ≥80% for browser_engine components.
5. **Fonts/text**: unit specs for nogc text_layout; bitmap+vector render
   position/size assertions vs chrome metrics; rendering buffer checks.
6. **Vulkan 2D**: run engine2d vulkan 8k checks live on this host (real GPU);
   assert no `[use-warning]`/de-JIT on vulkan modules; RenderDoc capture gate
   once renderdoccmd installed.
7. **HWIR path check**: fix the 21 hwir_foundation failures; resolve
   qualification CLI contract mismatch. Define + implement eager IR
   allocation for GPU offload; verify offload with HWIR on real GPU.
8. **SIMD/CUDA lanes**: x86 no-SIMD + SIMD runs green; CUDA offload +
   CUDA↔Vulkan parity green live.
9. **Doom**: add game2d web-canvas + gui backends; run doomgeneric on 2d,
   web, gui; frame_hash-based evidence. Improve 2d showcase.

Each phase: spipe SSpec tests, land via land.shs, higher-model review of
results before marking done.
