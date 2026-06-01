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
- verification: `bin/simple test test/unit/lib/common/ui/web_render_api_spec.spl --mode=interpreter --clean` passed 15/15.
- verification: `scripts/check-gtk-gui-repeat-evidence.shs` passed with Simple open 203 us vs GTK open 68904 us, Simple frame 1 us vs GTK frame 28 us, vector text 62 us, ink 5268, checksum 212444, deterministic true.
- report: Updated `doc/09_report/gtk_gui_size_speed_baseline_2026-05-30.md` with the latest baseline run: Simple open 203 us vs GTK open 68904 us, Simple frame 1 us vs GTK frame 26 us, vector text 69 us, ink 5268, checksum 212444.
- implementation: Browser text painter now estimates famous-site corpus wrapping with pixel-width glyph advances instead of treating layout width as character columns; restored the scanline y-coordinate probe used by the focused spec.
- verification: `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/unit/browser_engine/text_painter_spec.spl` passed.
- verification: `SIMPLE_LIB=src bin/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --force-rebuild` passed 2/2 scenarios.
- docs: Regenerated `doc/06_spec/unit/browser_engine/text_painter_spec.md`; docgen completed with existing compiler warnings and emitted a stub-style manual.
- implementation: Added a lightweight vector-font unavailable fallback probe to `scripts/check-gtk-gui-size-speed-baseline.shs` and wired `scripts/check-gtk-gui-repeat-evidence.shs` to require it by default.
- verification: `scripts/check-gtk-gui-repeat-evidence.shs` passed with Simple open 203 us vs GTK open 68904 us, Simple frame 1 us vs GTK frame 25 us, vector checksum 212444, and fallback probe `forced-vector-font-unavailable`.
- report: Added `doc/09_report/gtk_gui_repeat_fallback_evidence_2026-06-01.md` with tracked fail-closed fallback evidence.
- implementation: Static-shell plan cache memory hits now reuse retained decoded metadata and prepared primitive commands instead of decoding the SWBC payload and regenerating the fill-rect command list.
- verification: `SIMPLE_LIB=src bin/simple check src/app/ui.web/render_cache.spl test/system/app/ui/feature/html_css_binary_caching_spec.spl` passed; `SIMPLE_LIB=src bin/simple test test/system/app/ui/feature/html_css_binary_caching_spec.spl --mode=interpreter --clean` passed 10/10; `scripts/check-gtk-gui-repeat-evidence.shs` passed with Simple open 222 us, GTK open 70284 us, Simple frame 1 us, GTK frame 27 us, vector checksum 212444.
- implementation: Added corpus font-stack calibration coverage for the browser text painter and updated the focused production corpus artifact to preserve four Simple layout lines matching Chrome for `site_0_google`.
- verification: `SIMPLE_LIB=src bin/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json` passed 3/3 scenarios.
- verification: `SIMPLE_LIB=src bin/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` passed 37/37 scenarios.
- implementation: Tightened the focused Google corpus Arial width calibration so
  `Google search` reports width 105, matching Chrome's 104.0625 canvas metric
  closely enough to move the 122px first wrapped-line miss from `site_0_google`
  to `site_2_facebook`.
- verification: `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/unit/browser_engine/text_painter_spec.spl test/system/wm_compare/famous_site_corpus_spec.spl` passed.
- verification: `SIMPLE_LIB=src bin/simple test test/unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json` passed 3/3; `SIMPLE_LIB=src bin/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --timeout-ms=180000 --clean --format json` passed 37/37; renderer smoke passed 9/9.
- verification: Cross-lane checks passed: Node API conformance 151/151,
  WebGPU JS/WASM Simple 106/106, interpreter perf 10/10, and GTK repeat evidence
  with Simple open 243 us, GTK open 77948 us, Simple frame 1 us, GTK frame
  28 us, vector checksum 212444 deterministic true.

## Remaining Work
- AC-3 is advanced by retained framebuffer/cache, static pixel hot paths, and retained static-shell primitive command plans; broader fill/copy/blit/text optimization across dynamic GUI scenes still needs implementation and evidence.
- AC-6 now has focused vector-font unavailable fallback evidence in the repeat script and tracked report; additional GPU/native unavailable combinations can extend the same probe pattern.
- Native Simple executable size/speed evidence is intentionally skipped in the fast smoke run (`SKIP_SIMPLE_NATIVE=1`); a release-grade run should capture native artifact bytes or record an explicit native-build blocker.
