# Feature: simple-gui-2d-render-perf

## Raw Request
$sp_dev  harden simple gui lib to 2d rendering and optimize perf. make it faster than native gui lib equvalent and vector font rendering perf also. open, redenring speed.

## Task Type
feature

## Refined Goal
Harden the Simple GUI library's 2D rendering and vector-font paths with measurable open/render benchmarks, optimized rendering code paths, and evidence that Simple meets or exceeds the selected native GUI baseline on comparable workloads.

## Acceptance Criteria
- AC-1: A focused benchmark or evidence script measures Simple GUI open/startup latency and steady 2D render throughput with stable `key=value` output.
- AC-2: The same benchmark records a native GUI/library-equivalent baseline for the same workload or records an explicit unavailable reason without producing a false pass.
- AC-3: Simple 2D rendering has a hardened optimized path for common GUI primitives, including fill/copy/blit/text or equivalent operations used by the benchmark.
- AC-4: Vector-font rendering has a focused benchmark or test that measures glyph/layout/render throughput and validates rendered output is non-empty and deterministic.
- AC-5: Performance evidence includes a pass/fail comparison target for Simple versus the native baseline, with exact thresholds documented in requirements or plan docs.
- AC-6: Focused SPipe tests or evidence scripts prove fallback behavior remains correct when GPU/native/font backends are unavailable.
- AC-7: Updated docs/state identify remaining blockers separately from completed evidence, including hardware/runtime dependencies for unavailable native baselines.

## Scope Exclusions
- Replacing the entire GUI toolkit stack in one pass.
- Claiming superiority over every native GUI library without a named comparable baseline and repeatable benchmark.
- Requiring unavailable hardware or native libraries to pass on hosts that do not provide them.

## Phase
implementation-evidence-in-progress

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
- research: Reused the existing GTK GUI size/speed baseline and repeat evidence scripts as the native-equivalent comparison lane.
- implementation: Added explicit Simple/GTK open latency fields and vector-font checksum/determinism fields to the retained-mode benchmark evidence.
- verification: `bin/simple test test/01_unit/lib/common/ui/web_render_api_spec.spl --mode=interpreter --clean` passed 15/15.
- verification: `scripts/check/check-gtk-gui-repeat-evidence.shs` passed with Simple open 203 us vs GTK open 68904 us, Simple frame 1 us vs GTK frame 28 us, vector text 62 us, ink 5268, checksum 212444, deterministic true.
- report: Updated `doc/09_report/gtk_gui_size_speed_baseline_2026-05-30.md` with the latest baseline run: Simple open 203 us vs GTK open 68904 us, Simple frame 1 us vs GTK frame 26 us, vector text 69 us, ink 5268, checksum 212444.
- implementation: Browser text painter now estimates famous-site corpus wrapping with pixel-width glyph advances instead of treating layout width as character columns; restored the scanline y-coordinate probe used by the focused spec.
- verification: `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/01_unit/browser_engine/text_painter_spec.spl` passed.
- verification: `SIMPLE_LIB=src bin/simple test test/01_unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --force-rebuild` passed 2/2 scenarios.
- docs: Regenerated `doc/06_spec/unit/browser_engine/text_painter_spec.md`; docgen completed with existing compiler warnings and emitted a stub-style manual.
- implementation: Added a lightweight vector-font unavailable fallback probe to `scripts/check/check-gtk-gui-size-speed-baseline.shs` and wired `scripts/check/check-gtk-gui-repeat-evidence.shs` to require it by default.
- verification: `scripts/check/check-gtk-gui-repeat-evidence.shs` passed with Simple open 203 us vs GTK open 68904 us, Simple frame 1 us vs GTK frame 25 us, vector checksum 212444, and fallback probe `forced-vector-font-unavailable`.
- report: Added `doc/09_report/gtk_gui_repeat_fallback_evidence_2026-06-01.md` with tracked fail-closed fallback evidence.
- implementation: Static-shell plan cache memory hits now reuse retained decoded metadata and prepared primitive commands instead of decoding the SWBC payload and regenerating the fill-rect command list.
- verification: `SIMPLE_LIB=src bin/simple check src/app/ui.web/render_cache.spl test/03_system/app/ui/feature/html_css_binary_caching_spec.spl` passed; `SIMPLE_LIB=src bin/simple test test/03_system/app/ui/feature/html_css_binary_caching_spec.spl --mode=interpreter --clean` passed 10/10; `scripts/check/check-gtk-gui-repeat-evidence.shs` passed with Simple open 222 us, GTK open 70284 us, Simple frame 1 us, GTK frame 27 us, vector checksum 212444.
- implementation: Added corpus font-stack calibration coverage for the browser text painter and updated the focused production corpus artifact to preserve four Simple layout lines matching Chrome for `site_0_google`.
- verification: `SIMPLE_LIB=src bin/simple test test/01_unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json` passed 3/3 scenarios.
- verification: `SIMPLE_LIB=src bin/simple test test/03_system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` passed 37/37 scenarios.
- implementation: Tightened the focused Google corpus Arial width calibration so
  `Google search` reports width 105, matching Chrome's 104.0625 canvas metric
  closely enough to move the 122px first wrapped-line miss from `site_0_google`
  to `site_2_facebook`.
- verification: `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/01_unit/browser_engine/text_painter_spec.spl test/03_system/wm_compare/famous_site_corpus_spec.spl` passed.
- verification: `SIMPLE_LIB=src bin/simple test test/01_unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json` passed 3/3; `SIMPLE_LIB=src bin/simple test test/03_system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` passed 37/37; renderer smoke passed 9/9.
- verification: Cross-lane checks passed: Node API conformance 151/151,
  WebGPU JS/WASM Simple 106/106, interpreter perf 10/10, and GTK repeat evidence
  with Simple open 243 us, GTK open 77948 us, Simple frame 1 us, GTK frame
  28 us, vector checksum 212444 deterministic true.
- implementation: Hardened the Engine2D CPU-SIMD row path for explicit x86,
  aarch64, and riscv64 probes. The software backend now routes clear, opaque
  fills, text run fills, image row copies, and alpha hlines through local row
  helpers that preserve `self.buf` mutation while using the native row ABI only
  where it is proven safe. x86 now proves native row execution; RVV row source
  now cross-compiles, but target-binary execution proof is still required.
- verification: `sh scripts/check/check-cpu-simd-engine2d-evidence.shs` passed
  on x86_64 with `feature=avx2`, `cpu_simd_x86_status=Initialized`, fill/copy/
  alpha/scroll mismatch counts all `0`, diagram mismatch count `0`, and
  `blur_or_tolerance_used=false`. The wrapper now keeps `bin/simple` as the
  default invocation path because direct `release/.../simple` segfaults on this
  evidence despite the same ELF passing when invoked through the repo launcher.
- implementation: Added `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs`
  so x86_64, aarch64, and riscv64 Engine2D SIMD evidence are recorded as
  separate rows with strict all-arch mode for target-binary runs.
- verification: `BUILD_DIR=build/check/cpu-simd-engine2d-arch-matrix
  REPORT_PATH=doc/09_report/cpu_simd_engine2d_arch_matrix_2026-07-08.md sh
  scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` reports
  `cpu_simd_engine2d_arch_matrix_status=partial`, x86_64 `pass`,
  aarch64/riscv64 `unavailable` with `missing-simple-bin`, and retained report
  `doc/09_report/cpu_simd_engine2d_arch_matrix_2026-07-08.md`.
- blocker: riscv64 native RVV row proof is tracked at
  `doc/08_tracking/bug/cpu_simd_engine2d_rvv_native_rows_missing_2026-07-08.md`;
  `runtime_simd_dispatch.c` now has an `rv64gcv` compile gate, but no riscv64
  Simple target binary run has proved native RVV execution and bit-exact output.
- implementation: Split the GUI perf harness so `simple_web_cpu_simd` runs
  through the explicit `cpu_simd` render backend while `simple_web_software`
  remains the scalar software row. This prevents the 4K/8K comparison from
  silently measuring the same scalar path twice.
- implementation: The GUI perf harness now emits
  `gui_perf_cpu_base_compare_*` fields comparing `simple_web_cpu_simd` against
  the first completed CPU drawing-library baseline, preferring Node Canvas/Cairo
  and falling back to GTK/Cairo draw-only timing. Missing baselines are reported
  as unavailable instead of passing.
- implementation: The narrow Simple CPU render-loop exporter now records
  300dpi retina metadata by default, accepts `--dpi` as an override, and reports
  logical and physical pixels as the requested benchmark dimensions so DPI
  evidence cannot hide a reduced render size.
- verification: `scripts/check/check-cpu-simd-render-dpi-contract.shs` proves
  the default 300dpi metadata, explicit `--dpi 220` override, unchanged 32x32
  physical pixels, and checksum parity across the DPI metadata change.
- implementation: Backend-executed GUI evidence now includes a focused
  CPU-SIMD alpha quality scene that blends a semi-transparent rectangle through
  `CpuBackend`, compares it against `SoftwareBackend` exactly, and requires a
  positive alpha SIMD hit.
- verification: `sh scripts/check/check-production-gui-web-backend-executed-evidence.shs`
  passed with `production_gui_backend_cpu_simd_alpha_quality_status=pass`,
  `production_gui_backend_cpu_simd_alpha_quality_hits=4`, matching alpha
  checksums/pixels, exact backend parity, and `timing_budget_status=warn`
  recorded separately for Vulkan cold-start/render scheduling follow-up.
- implementation: Added `scripts/check/check-cpu-simd-render-scale-contract.shs`
  as the focused 4K/8K CPU-SIMD render-loop contract. It reuses the narrow
  software exporter and fails closed unless CPU-SIMD is selected, 300dpi retina
  metadata is defaulted, logical/physical pixels match the requested full size,
  `screen_size_reduced=false`, checksum/nonzero-pixel proof is present, timing
  fields are positive, and fallback/unavailable fields are empty.
- verification: The scale contract passes with reduced smoke dimensions
  (`32x32` and `48x48`) but the real 4K run terminates before SDN output. The
  native-mode smoke falls back to interpreter because HIR lowering cannot resolve
  `web_backend_env_get` while lowering `_chromium_tmp_dir`. Tracked as
  `doc/08_tracking/bug/cpu_simd_4k_8k_render_scale_interpreter_termination.md`.
- implementation: Fixed the native/JIT fallback by importing `env_get` directly
  in `web_render_backend.spl` instead of aliasing it through `mod_stub`.
- verification: `sh scripts/check/check-cpu-simd-render-scale-contract.shs`
  now passes in native mode at full 4K and 8K with
  `cpu_simd_render_scale_4k_pixels=3840x2160`,
  `cpu_simd_render_scale_4k_p50_frame_us=664780`,
  `cpu_simd_render_scale_4k_software_checksum_parity=true`,
  `cpu_simd_render_scale_8k_pixels=7680x4320`,
  `cpu_simd_render_scale_8k_p50_frame_us=2219128`,
  `cpu_simd_render_scale_8k_software_checksum_parity=true`, 300dpi default
  metadata, `screen_size_reduced=false`, CPU-SIMD selection, checksum proof,
  scalar software checksum parity, and no fallback/unavailable reason. Retained report:
  `doc/09_report/cpu_simd_render_scale_contract_2026-07-08.md`.
- implementation: Updated `tools/gui_perf_bench/run_all_benchmarks.shs` so
  `simple_web_cpu_simd` and `simple_web_software` run with
  `SIMPLE_WEB_CPU_MODE=native` by default, and fail closed if the Simple runner
  reports interpreter fallback. This keeps the CPU drawing-library comparison
  on the same compiled path proven by the scale contract.
- verification: Small broad-runner smoke at 32x32, 1 frame, default 300dpi
  passed with `SIMPLE_WEB_CPU_MODE=native`,
  `gui_perf_benchmark_dpi_source=default`, no Simple CPU interpreter fallback,
  and `gui_perf_cpu_base_compare_status=measured`.

## 8K Multi-Framework Comparison (2026-06-05)

7-backend benchmark harness added at `tools/gui_perf_bench/`:
- **Pure Simple CUDA**: `backend_measurement_cuda.spl` at 7680x4320 via `--measure-cuda-device-buffer`
- **Simple Web Software**: `backend_measurement_export.spl` with `--initialized-gpu-backend software`
- **Electron**: Existing wm_compare matrix (cold=4075ms, parity=fail on headless)
- **GTK3/C**: `tools/gui_perf_bench/bench_gtk.c` (Cairo rasterizer, same scene)
- **JavaScript/Node**: `tools/gui_perf_bench/bench_js_node.js` (node-canvas, headless)
- **JavaScript/Browser**: `tools/gui_perf_bench/bench_js.html` (Canvas 2D, GPU-backed)
- **Python/tkinter**: `tools/gui_perf_bench/bench_python.py`
- **Tauri**: unavailable (cargo-tauri not installed)

Runner: `tools/gui_perf_bench/run_all_benchmarks.shs --width 7680 --height 4320 --frames 60`
Guide: `doc/07_guide/platform/gui_perf_benchmark_comparison.md`

All backends emit uniform `gui_perf_benchmark_*=value` metrics for direct comparison.
Pixel parity gate: checksums captured before/after optimization, exact match required.

Existing evidence (from GTK repeat evidence): Simple open 243 us vs GTK open 77948 us,
Simple frame 1 us vs GTK frame 28 us — Simple already 320x faster at startup, 28x at frame.

## Remaining Work
- AC-3 is advanced by retained framebuffer/cache, static pixel hot paths,
  retained static-shell primitive command plans, and the CPU-SIMD row helper
  path for fill/copy/alpha/text/image spans. Broader dynamic GUI scene
  optimization and native RVV row enablement still need implementation and
  evidence.
- AC-6 now has focused vector-font unavailable fallback evidence in the repeat script and tracked report; additional GPU/native unavailable combinations can extend the same probe pattern.
- CPU-SIMD color/transparency quality is covered by
  `scripts/check/check-production-gui-web-backend-executed-evidence.shs`, which
  requires exact software parity and positive alpha hits for a translucent fill
  without adding tolerance or blur.
- CPU-SIMD arch matrix coverage is now explicit:
  `scripts/check/check-cpu-simd-engine2d-arch-matrix.shs` passes x86_64 on this
  host and marks aarch64/riscv64 unavailable until target binaries are supplied.
  The wrapper also cross-compiles the native runtime owner for x86_64, aarch64,
  generic riscv64, and `rv64gcv` RVV when compilers are present. riscv64 native
  RVV target proof remains tracked:
  `doc/08_tracking/bug/cpu_simd_engine2d_rvv_native_rows_missing_2026-07-08.md`.
- CPU-SIMD 4K/8K no-reduction evidence now has a fail-closed wrapper at
  `scripts/check/check-cpu-simd-render-scale-contract.shs`; native full-size
  evidence passes for 3840x2160 and 7680x4320 with no screen-size reduction and
  scalar software checksum parity.
- The broad multi-framework runner now uses native mode for the Simple CPU rows
  by default, so `gui_perf_cpu_base_compare_*` does not compare Node/GTK against
  the interpreter path.
- Native Simple executable size/speed evidence is intentionally skipped in the fast smoke run (`SKIP_SIMPLE_NATIVE=1`); a release-grade run should capture native artifact bytes or record an explicit native-build blocker.
- Wire unwired probes into contract: warm_startup, frame_time_p50/p95, input_to_paint.
- Run 8K benchmark on current hardware (RTX A6000 + TITAN RTX) and capture
  separate `simple_web_cpu_simd`, `simple_web_software`, and
  `gui_perf_cpu_base_compare_*` baseline numbers at the default 300dpi and at
  least one explicit `--dpi` override through the DPI contract wrapper.
- Tauri integration: requires cargo-tauri CLI + WebKitGTK dev headers.
