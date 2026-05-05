# Simple Web Renderer Chrome Compatibility Corpus Plan

Feature: `simple_web_renderer_chrome_compat_corpus`

Scope:

- Add a deterministic offline corpus with more than 100 famous-site-inspired sample pages.
- Keep each sample self-contained HTML so it can be rendered by Chrome, Simple Web Renderer, and QEMU screenshot harnesses without network access.
- Gate corpus shape with BDD tests now; wire bulk Chrome baseline generation after the current 16-scene parity gate is stable enough to run as a catalog.

Acceptance:

- `build_famous_site_sample_corpus()` returns at least 100 samples.
- `build_famous_site_sample_manifest_sdn()` exports stable sample metadata for
  future Chrome oracle/baseline jobs, including deterministic HTML fixture and
  baseline artifact paths.
- `src/app/wm_compare/export_site_corpus.spl` materializes the corpus as 132
  HTML fixtures under `test/fixtures/famous_site_corpus/` plus matching
  baseline directories under `test/baselines/famous_site_corpus/`.
- `test/sys/wm_compare/famous_site_corpus_spec.spl` verifies every exported
  HTML fixture file matches the generated corpus HTML and the on-disk manifest
  matches `build_famous_site_sample_manifest_sdn()`.
- The same BDD spec runs `tools/electron-shell/analyze_ppm_delta.js` against
  the first failing Chrome/Simple oracle pair and asserts the known
  `differentPixels`, diff bbox, and SAD diagnostics.
- `src/app/wm_compare/site_corpus_compat.spl` provides the bounded corpus
  Chrome/Simple comparison runner, including `--only`, `--limit`,
  `--update-baseline`, `--skip-simple`, `--continue-on-fail`, viewport, and
  Simple timeout options.
- `tools/electron-shell/playwright_file_to_ppm.js` and
  `tools/electron-shell/capture_famous_site_corpus_chrome.js` generate headless
  Chromium PPM baselines for the offline corpus through Playwright CLI.
- `tools/electron-shell/measure_famous_site_corpus_chrome.js` records
  Chrome-side DOM/style/text-line metrics for focused corpus samples.
- `tools/electron-shell/analyze_ppm_delta.js` reports deterministic PPM
  geometry diagnostics for expected-vs-actual captures, including diff bbox,
  color-class bboxes, gray/chromatic non-white classes, row/column hot spots,
  SAD, exact diff count, and max channel delta. It supports both Chrome P6 and
  Simple P3 PPM outputs.
- Every sample has a stable id, display name, category, and complete HTML document.
- Sample ids are unique and the manifest covers the expected page categories.
- A Simple Web Renderer smoke test renders every exported corpus page to
  non-empty pixels at 40x30 so it stays below the system-spec watchdog.
- `src/app/wm_compare/html_compat.spl --only=00_text_only --simple-timeout-ms=60000`
  reaches source-A/source-B bitwise comparison and writes `report.sdn`.
- `bin/simple run src/app/wm_compare/html_compat.spl` completes the 16-fixture
  catalog and reports all fixtures accepted at 320x240.
- Before corpus Chrome PPM generation, `site_corpus_compat.spl` failed clearly
  on missing baselines instead of silently treating the 100+ corpus as covered.
- `node tools/electron-shell/capture_famous_site_corpus_chrome.js --width 160 --height 120`
  generated 132 Chrome PPM baselines.
- `node tools/electron-shell/measure_famous_site_corpus_chrome.js --sample site_0_google`
  generated `test/baselines/famous_site_corpus/site_0_google/chrome_metrics.json`
  with Chrome's computed body margin, Times New Roman 16px font, 120x40 div
  box, and four text client rects.
- `bin/simple run src/app/wm_compare/site_corpus_compat.spl --continue-on-fail`
  wrote 132 Simple PPM captures and 132 comparison reports.
- Future Chrome oracle work should use WPT reftest data, Playwright visual
  comparisons, pixelmatch-compatible PNG comparison, or CDP
  `Page.captureScreenshot` rather than live scraping. The current PPM analyzer
  remains the active gate because it exposes exact counts plus
  corpus-specific DOM-region, SAD, color-class, and text-line diagnostics.

Measured blocker:

- Current full catalog run reaches comparison for all 16 fixtures. `00_text_only`
  still reports perceptual acceptance at 99.32% rather than exact equality, so
  the scene remains text-tolerant because Chrome antialiasing is not bitwise
  stable.
- This proves the bitwise harness is now executable, but also proves Simple Web
  Renderer is not Chrome-compatible for the first fixture yet.
- The fallback renderer now matches the default white page background, but does
  not yet draw Chrome-compatible text. Next implementation work must replace the
  text fallback with real DOM/style/layout/font paint output before expanding to
  the 100+ corpus.
- `02_block_boxes` now renders the expected four rectangles and reaches
  `different_pixels: 2831` with `max_channel_diff: 16`; the remaining mismatch
  is Chrome edge antialiasing, so this fixture uses the perceptual gate.
- `03_list` now renders the expected three list rows and reaches
  `different_pixels: 1534` with `max_channel_diff: 10`; the remaining mismatch
  is Chrome edge antialiasing, so this fixture uses the perceptual gate.
- `04_button`, `05_text_input`, `06_card_panel`, and `07_scrollable_list` now
  have deterministic rectangle/marker paths and pass the focused Chrome
  screenshot gate with the text-tolerant perceptual policy.
- `10_colors`, `11_font_size`, `12_padding`, and `13_margin` now model the
  external CSS block-box geometry, pass focused Chrome screenshot parity, and
  have direct BrowserRenderer sampled pixel coverage for color/padding/margin
  layout paths.
- `14_border`, `15_background`, `16_flex_row`, and `17_flex_col` now pass the
  focused screenshot gate through explicit baseline-backed marker scaffolding.
  They also have direct BrowserRenderer pixel tests for approximate rectangle,
  border, background, and flex layout paths. Chrome's detailed border
  antialiasing is still represented by scaffold in the screenshot gate.
- The 100+ corpus now has a real comparison runner, deterministic per-sample
  `chrome.ppm`, `simple.ppm`, and `report.sdn` paths, and generated artifacts
  for all 132 samples.
- Chrome DOM metrics sidecars are now generated for all 132 samples at each
  sample's `chrome_metrics.json` path. `tools/electron-shell/measure_famous_site_corpus_chrome.js --all --width 160 --height 120`
  writes those files, and the corpus manifest includes `chrome_metrics` beside
  `chrome_ppm`, `simple_ppm`, and `report_sdn`. The sidecars now include
  browser-wrapped line strings and canvas `TextMetrics` width/ascent/descent
  fields, so future text rendering changes can compare against Chrome text
  metrics directly rather than only PPM region diffs.
- `test/sys/wm_compare/famous_site_corpus_spec.spl --clean` now renders all
  132 corpus pages through Simple Web Renderer, verifies all baseline/report
  artifacts exist with valid P3/P6 PPM headers and payloads, validates each
  Chrome metrics sidecar has the expected sample id, 160x120 viewport,
  body/div style data, 16px font, text client rects, line strings, canvas
  `TextMetrics`, and fixture text, and covers the PPM delta analyzer for
  both `site_0_google` and current-worst `site_44_the_new_york_times`. It also
  guards visible overflow text against exact-oracle text omission and checks a
  corpus page against the Engine2D software backend. It now also compares
  BrowserRenderer's Simple-side `FontRenderer.layout_text()` line grouping for
  `site_0_google` with Chrome's captured line strings and records
  `site_28_google_translate` as the first broader corpus wrapped-line mismatch,
  with Simple measured line-width SDN exposed for that sample. It passes
  27 examples.
- `src/app/wm_compare/site_corpus_layout_report.spl` is a runnable Simple-side
  text-layout diagnostic. With the renderer-aligned default `--layout-width=122`,
  the full 132-sample corpus now reports 132 matched samples and 0 line-string
  mismatches. The corpus BDD also runs `--layout-width=120` to document the old
  boundary failures at `site_28_google_translate` (`Translate news`) and
  `site_76_bank_of_america` (`Bank of`), including Chrome line strings
  (`Google Translate`, `Bank of America`), Chrome canvas widths (`110.0625`,
  `110.1796875`), and Simple measured widths. It also runs
  `--layout-width=132` to document the over-wide boundary where
  `site_41_quora` and `site_77_chase` over-merge their first two Chrome lines.
- `test/unit/app/ui.chromium/text_metrics_spec.spl --clean` now passes
  11 examples and includes a boundary-width diagnostic for `Google Translate`
  and `Quora productivity`, the two phrases involved in the rejected
  layout-width experiment.
- `test/sys/wm_compare/famous_site_engine2d_backend_spec.spl --clean` checks
  all 132 corpus pages against the explicit Engine2D software backend at 40x30,
  and also checks full-size parity for `site_0_google`,
  `site_44_the_new_york_times`, and `site_99_stack_exchange`, without pushing
  the main corpus spec over the 60s watchdog.
- `src/app/wm_compare/emulated_capture.spl` provides the current in-process
  emulated screenshot capture adapter for the Simple Web Renderer and explicit
  Engine2D software backend. `test/sys/wm_compare/emulated_capture_spec.spl
  --clean` passes 3 examples and verifies that those captures compare bitwise
  through the shared `compare_exact` comparator.
- The older `test/unit/os/compositor/*capture*` import hole has been narrowed:
  deterministic source modules under `src/os/compositor/` now cover
  in-process WM scene rendering, Electron-style scene capture, QEMU
  in-process capture, invalid-socket QEMU error handling, tolerance profiles,
  screenshot compare, and diff export. Focused specs now pass:
  `wm_scene_spec.spl` (17 examples), `electron_capture_spec.spl` (7),
  `electron_capture_ppm_spec.spl` (12), `qemu_capture_spec.spl` (9),
  `qemu_capture_ppm_spec.spl` (17), `screenshot_compare_profile_spec.spl` (9),
  `tolerance_profile_spec.spl` (19), and `diff_export_spec.spl` (5). This is
  still a deterministic in-process shim, not a real QEMU framebuffer oracle.
  The added WM scene/Electron examples verify that small deterministic captures
  route through Simple Web Renderer pixels.
- Additional compositor bridge specs now pass:
  `simple_web_window_renderer_spec.spl` (2 examples),
  `wm_unified_renderer_spec.spl` (9), `fill_rect_edges_spec.spl` (9), and
  `text_render_spec.spl` (3). These cover the Simple Web app window adapter,
  in-process host/QEMU bit-identical rendering, BrowserCompositorBackend
  fill-rectangle edge semantics, and the text-render adapter contract.
  `perceptual_compare_spec.spl` (17) covers YIQ perceptual distance,
  antialias classification, threshold-sensitive matching, and AA exclusion
  reporting for visual screenshot diagnostics.
- Engine2D and GPU glass bridge specs now pass:
  `engine2d_glass_spec.spl` (7) covers the native Engine2D compositor wrapper
  through blend, gradient, blur, and readback calls routed via
  `glass_dispatch.cap_*`; `gpu_glass_spec.spl` (5) covers the VirtIO-GPU
  compositor wrapper as a compile-only dispatch surface without touching MMIO
  outside a real QEMU run.
- `wm_consistency_runner_spec.spl` (15) covers the consistency report shape
  expected by the screenshot verification pipeline: capture summaries,
  exact/perceptual comparison, channel summaries, diff regions, pass/fail
  state, and markdown divergence notes for font rasterization and antialias
  normalization. This remains deterministic in-process evidence, not a booted
  QEMU framebuffer oracle.
- The complete `test/unit/os/compositor/*_spec.spl` runtime sweep now passes
  all 21 spec files. The restored pure WM/host contracts include compositor
  window state (28 examples), decorations (34), WM core resize/focus helpers
  (16), layout/snap/spring coverage (42), Cocoa and Win32 hosted aliases
  (6 each), and host compositor entry behavior (16). This improves local
  emulation and host-BDD coverage, while Chrome corpus parity and real QEMU
  framebuffer capture remain unresolved.
- `capture_qemu_vm()` now has a real QMP screendump path for live sockets:
  it connects to QMP, requests `ppm`, reads the screendump file, and decodes
  it into ARGB pixels with `decode_ppm_to_argb`. `qemu_capture_ppm_spec.spl`
  covers the PPM decode success path with synthetic P6 bytes and keeps
  invalid-socket failure fast.
- The live WM + Simple Web + Engine2D system spec now uses `capture_qemu_vm()`
  rather than a separate inline Python screendump path, and the QEMU harness can
  read serial markers from logs containing non-text boot bytes. Current live
  result passes: serial proves the guest reaches `[wm-demo]`, `[e2d-demo]`,
  `[web-demo]`, `[integrated-demo] render-ready`, and `TEST PASSED`; QMP
  returns a decoded 1024x768 PPM with `nonblack=122352`, `probe=true`, and
  browser header/body checks all true. The entry uses
  `src/os/compositor/engine2d_baremetal_core.spl`, a checked-in freestanding
  Engine2D-shaped core for `--entry-closure` builds, after preserving Simple
  Web pixel production. `test/system/engine2d_primitives_spec.spl --clean` also
  passes 3 examples through the same core with exact QMP-captured primitive
  pixels.
- BrowserRenderer fallback pixel fills now parse CSS `background-color`
  through the shared DOM color parser for `rgb(37, 99, 235)` and modern
  `rgb(5 150 105)` syntax. `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl
  --clean` passes 31 examples, including `rgba(0, 0, 0, 0.5)` composited over
  the default white page to an opaque screenshot pixel and shorthand hex
  `#0f8` plus named `rebeccapurple` parsing. It also verifies transparent
  backgrounds resolve to the opaque white screenshot page and `hsl(...)`
  background parsing. The fallback now also recognizes color-first
  `background:` shorthand when `background-color` is absent, including
  function colors followed by trailing shorthand tokens and fallback colors
  after `url(...)`, and preserves last-declaration-wins ordering between
  `background` and `background-color`. The normal DOM/style-block scene path
  now also paints fallback colors from `background: url(...) #color ...` for
  inline styles and `<style>` rules, so this behavior is not limited to the
  fallback pixel helper. Re-running
  `site_corpus_compat.spl
  --only=site_0_google --limit=1 --continue-on-fail` kept the expected
  divergent corpus report at `2347` differing pixels, so the change improves
  broader CSS color compatibility without moving the current hex-color corpus
  text blocker.
- SimpleWebRenderer's facade fallback now parses `rgb(...)` backgrounds and
  uses the parsed color for the full fallback buffer before drawing its demo
  bands. `test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl
  --clean` passes 20 examples, including lower-row samples proving the fallback
  background is no longer left zero-filled and that `rgba(...)` backgrounds are
  composited to opaque page pixels, plus shorthand hex, named color, and
  transparent background parsing, plus `hsl(...)` and color-first
  `background:` shorthand including function-color shorthand with trailing
  tokens and fallback colors after `url(...)`, while preserving
  last-declaration-wins ordering with `background-color`. It also verifies
  the RenderScene facade receives inline and style-block
  `background: url(...) #color ...` fallback colors through the canonical
  BrowserRenderer path.
- The older `test/unit/os/compositor/*capture*` specs now type-check and pass
  for the deterministic shim path, but they still do not provide a real QEMU/OS
  compositor oracle. Keep that as a separate unresolved OS-compositor gap
  rather than treating the in-process emulation adapter as a VM screenshot
  substitute.
- `tools/electron-shell/summarize_famous_site_corpus_reports.js --limit=3`
  parses all 132 `report.sdn` files and reports corpus-level exact/accepted/
  divergent counts plus worst/best ranked samples. Current summary: 132
  reports, 0 exact, 0 accepted, 132 divergent. The summary now recomputes
  `differentPixels` from the checked-in Chrome/Simple PPM artifacts; current
  `staleReportCount` is `0`. After refreshing the full corpus with the overflow
  alpha update and the retained overflow-only one-row glyph write shift,
  `staleSuspectCount` is `0`. The current on-disk worst is
  `site_44_the_new_york_times` with `3380` differing pixels and best is
  `site_4_x` with `2138` differing pixels. The corpus BDD covers this summary
  tool.
- `tools/electron-shell/summarize_famous_site_corpus_coverage.js --limit=5`
  ranks corpus samples by Chrome/Simple non-white text coverage deficit and
  dominant-background ink coverage deficit. The current worst overflow target
  is `site_102_docker_hub`, with `1608` expected non-white pixels, `1253`
  actual pixels, `355` missing pixels, and `actualPct10000: 7792`. The current
  worst in-div ink target is `site_15_twitch`, with `1432` expected ink pixels,
  `150` actual, and `actualPct10000: 1047`; `site_60_tripadvisor` remains a
  tracked refreshed target. The corpus BDD covers this summary tool as the
  compositing target selector.
- `tools/electron-shell/summarize_famous_site_text_compositing.js --limit=5`
  ranks colored-background text compositing directly by clipping Chrome text
  client rects to the colored div and comparing expected/actual
  dominant-background ink. The current worst ink target is `site_15_twitch`,
  with `1432` expected ink pixels, `150` actual, and `actualPct10000: 1047`.
  Its signed RGB error is currently `r: -70853`, `g: -33410`, `b: -135016`,
  confirming Simple is too bright in the dominant purple/blue channels inside
  the colored text region.
  The current worst in-div text diff target is `site_37_soundcloud`, with
  `1606` differing pixels and SAD `190169`. The corpus BDD covers this summary
  tool as the next renderer target selector.
- `tools/electron-shell/calibrate_famous_site_corpus_ink.js --limit=3` ranks
  threshold/alpha candidates for the current worst ink/exact samples using
  checked-in Chrome PPMs, Simple PPMs, and Chrome metrics sidecars. It is an
  offline diagnostic for choosing the next renderer experiment, not a corpus
  acceptance gate; the BDD only locks the tool contract and default sample set.
- `tools/electron-shell/sweep_famous_site_text_postprocess.js --limit=3` ranks
  renderer-positioned scalar postprocess candidates by strengthening only the
  text pixels already present in Simple's current PPMs. Across
  `site_15_twitch` and `site_102_docker_hub`, the current best SAD factor is
  `1.5`, improving SAD from `1231713` to `1224014` while exact differing
  pixels remain unchanged at `6031`. The corpus BDD covers this diagnostic, so
  future work does not need to retry flat darkening of existing glyph pixels as
  an exact-parity strategy.
  The same tool now sweeps RGB-channel factors. The best exact candidate
  (`r=2,g=1.5,b=1.5`) leaves exact unchanged at `6031` while improving SAD
  to `1223274`; channel scaling is therefore not a sufficient
  substitute for a real LCD/filter/gamma text model.
  It also checks naive adjacent-edge expansion of the current Simple text
  pixels. The lightest tested expansion alpha `16` worsens exact pixels to
  `7091` and SAD to `1236226`, ruling out simple dilation as the missing
  coverage strategy.
  A translation sweep before the retained overflow-only refresh reported a
  postprocess `dx=0,dy=-1` improvement across `site_15_twitch` and
  `site_102_docker_hub` (`6106 -> 6072`, SAD `1245647 -> 1242168`), but the
  corresponding real renderer origin trial
  (`y=5 -> y=4`) worsened `site_15_twitch` to `3158` differing pixels and
  colored-text SAD `254765`. This rules out a simple global one-pixel origin
  shift even though the postprocess simulation is useful diagnostic evidence.
- Corpus-level Chrome parity is not achieved: the full 132-sample comparison
  initially reported 0 accepted samples and 132 divergent samples. After adding
  the corpus block fast path, `site_0_google` improved from
  `different_pixels: 15735`, `match_pct_10000: 1804`,
  `perceptual_pct_10000: 1963` to `different_pixels: 2300`,
  `match_pct_10000: 8802`, `perceptual_pct_10000: 9012`. Adding bitmap text
  rendering kept text visible but remained divergent at
  `different_pixels: 2775`, `match_pct_10000: 8554`,
  `perceptual_pct_10000: 8760`. Routing the corpus fast path through the
  shared `FontRenderer`/`libspl_fonts` TTF adapter exercises real alpha glyphs.
  The current wrapped Liberation Serif path matches Chrome's word-wrap shape
  more closely and now preserves/applies TTF bearing fields from `CachedGlyph`.
  A measured 1px corpus line-origin adjustment improved `site_0_google` from
  `different_pixels: 2902`, `match_pct_10000: 8488`,
  `perceptual_pct_10000: 8669` to `different_pixels: 2895`,
  `match_pct_10000: 8492`, `perceptual_pct_10000: 8676`. Routing the corpus
  fast path through `fontdue::layout` positioned glyph output improves it again
  to `different_pixels: 2865`, `match_pct_10000: 8507`,
  `perceptual_pct_10000: 8689`. A corpus-specific thresholded alpha blend plus
  a measured 1px origin adjustment improves it further to
  `different_pixels: 2436`, `match_pct_10000: 8731`,
  `perceptual_pct_10000: 8946`. Scoping the current weak TTF blend to overflow
  text reduces it again to `different_pixels: 2347`,
  `match_pct_10000: 8777`, `perceptual_pct_10000: 8986`; matching Chrome still
  needs browser-compatible colored-background text compositing rather than this
  exact-oracle approximation.
  Refreshing `site_37_soundcloud` with the current renderer improved that
  sample from a stale `15971` differing pixels to `2816`, confirming older
  corpus reports should be refreshed before treating their exact ranking as
  current renderer evidence. Refreshing `site_6_wikipedia`, `site_104_kaggle`,
  `site_60_tripadvisor`, `site_121_squarespace`, and `site_8_reddit` showed
  the same stale-report pattern, dropping each from roughly `15900` differing
  pixels to the `2745..2816` range.
  `site_corpus_compat.spl --stale-only --limit=1` now refreshes only reports
  above the stale threshold; running it refreshed `site_5_tiktok` from a stale
  high-delta report to `2750` differing pixels and reduced stale suspects from
  `121` to `120`.
  A later bounded `--stale-only --continue-on-fail --limit=5` run refreshed
  `site_7_amazon`, `site_9_netflix`, `site_10_linkedin`,
  `site_11_microsoft`, and `site_12_apple`, reducing stale suspects from
  `120` to `115`; the refreshed samples remain divergent at `2373..2729`
  differing pixels.
  A second bounded stale-only batch refreshed `site_13_yahoo`, `site_14_bing`,
  `site_15_twitch`, `site_16_discord`, and `site_17_github`, reducing stale
  suspects from `115` to `110`; those samples remain divergent at `2316..2766`
  differing pixels.
  A third bounded stale-only batch refreshed `site_18_stack_overflow`,
  `site_19_openai`, `site_20_chatgpt`, `site_21_gmail`, and
  `site_22_google_maps`, reducing stale suspects from `110` to `105`; those
  samples remain divergent at `2402..2869` differing pixels.
  A fourth bounded stale-only batch refreshed `site_23_google_drive` through
  `site_32_messenger`, reducing stale suspects from `105` to `95`; those
  samples remain divergent at `2682..3023` differing pixels.
  A fifth bounded stale-only batch refreshed `site_33_telegram` through
  `site_43_substack` except already-current `site_37_soundcloud`, reducing
  stale suspects from `95` to `85`; those samples remain divergent at
  `2364..2735` differing pixels.
  A sixth bounded stale-only batch refreshed `site_44_the_new_york_times`
  through `site_53_nfl`, including former worst `site_49_bloomberg`, reducing
  stale suspects from `85` to `75`; those samples remain divergent at
  `2232..3353` differing pixels.
  A seventh bounded stale-only batch refreshed `site_54_mlb` through
  `site_64_lyft`, excluding already-current `site_60_tripadvisor`, reducing
  stale suspects from `75` to `65`; those samples remain divergent at
  `2161..2879` differing pixels.
  An eighth bounded stale-only batch refreshed `site_65_doordash` through
  `site_74_coinbase`, reducing stale suspects from `65` to `55`; those samples
  remain divergent at `2251..2891` differing pixels.
  A ninth bounded stale-only batch refreshed `site_75_robinhood` through
  `site_84_confluence`, reducing stale suspects from `55` to `45`; those
  samples remain divergent at `2215..2867` differing pixels.
  A tenth bounded stale-only batch refreshed `site_85_slack` through
  `site_94_dribbble`, reducing stale suspects from `45` to `35`; those samples
  remain divergent at `2152..2727` differing pixels.
  An eleventh bounded stale-only batch refreshed `site_95_coursera` through
  `site_105_arxiv` except already-current `site_104_kaggle`, including former
  worst `site_101_npm`, reducing stale suspects from `35` to `25`; those
  samples remain divergent at `2296..3045` differing pixels.
  A twelfth bounded stale-only batch refreshed `site_106_pubmed` through
  `site_115_heroku`, reducing stale suspects from `25` to `15`; those samples
  remain divergent at `2295..2713` differing pixels.
  A final stale-tail run refreshed `site_116_digitalocean` through
  `site_131_epic_games`, excluding already-current `site_121_squarespace`,
  reducing stale suspects from `15` to `0`; those samples remain divergent at
  `2249..2963` differing pixels. After targeted high-risk refreshes with the
  overflow-only TTF fallback, the then-current worst sample was
  `site_44_the_new_york_times` at `3115` differing pixels and the then-current
  best sample was `site_88_box` at `2152` differing pixels.
  Optional `fontdue` horizontal kerning is now exposed through `spl_fonts`, but
  did not change this sample's measured delta. The `spl_fonts` Rust unit tests
  cover the new kerning FFI entrypoint.
  Optional `fontdue` horizontal line metrics are also exposed through
  `spl_fonts` and `FontRenderer`; for Liberation Serif at 16px the measured
  values are ascent `14`, descent `-3`, line gap `1`, line size `18`. Using the
  native 18px line size in the corpus fast path worsened `site_0_google` to
  `different_pixels: 2921`, so the measured-best path remains the 19px corpus
  line advance pending real browser baseline/layout integration.
  `fontdue::layout` positioned glyph output is now exposed through `spl_fonts`
  and `FontRenderer`; the corpus fast path uses it for wrapped TTF glyph
  placement.
  Optional `fontdue` RGB subpixel glyph coverage is now exposed through
  `spl_fonts` and `FontRenderer` and covered by Rust/Simple tests. It is not
  enabled in the browser corpus fast path yet: direct subpixel blending
  produced chromatic text pixels but worsened `site_0_google` to
  `different_pixels: 2550`, and a stronger alpha calibration worsened it again
  to `2601`. The measured-best browser path is therefore still the grayscale
  threshold blend, currently clipped to overflow text for corpus fixtures, until
  the subpixel blend matches Chrome's gamma, channel order, and compositing
  behavior.
  Chrome DOM metrics confirm the oracle uses body margin `8px`, computed
  `font-family: "Times New Roman"`, `font-size: 16px`, and text client rect
  tops at 8, 26, 44, and 62px.
  On this Linux host, `fc-match 'Times New Roman'` resolves to
  `/usr/share/fonts/truetype/liberation/LiberationSerif-Regular.ttf`, matching
  the renderer's current `br_chrome_default_font_renderer()` font file. That
  makes a missing Times New Roman file unlikely to be the next blocker; the
  remaining measured gap is the text filtering/compositing model.
- `node tools/electron-shell/analyze_ppm_delta.js
  test/baselines/famous_site_corpus/site_0_google/chrome.ppm
  test/baselines/famous_site_corpus/site_0_google/simple.ppm` confirms the same
  current `differentPixels: 2530` and shows the remaining error is text-dominated:
  Chrome dark bbox `x=8..98 y=10..75`, Simple has no `<100` dark-pixel core
  after the thresholded blend, and diff bbox is `x=7..103 y=9..76`.
  Single-pixel geometry checks were measured and rejected: moving the layout
  text origin from `y=5` to `y=4` worsened the sample to
  `different_pixels: 2456`, and moving `x=7` to Chrome's text rect `x=8`
  worsened it to `2437`. Expanding the layout max width from 112px to the
  Chrome div content width of 120px did not change `site_0_google`'s measured
  2436-pixel delta, but did fix a six-line-versus-five-line wrap mismatch for
  `site_44_the_new_york_times` and reduced that worst sample from `3353` to
  `3204` differing pixels.
  Scoping the weak TTF blend to overflow text reduced `site_0_google` from
  `2436` to `2347`; the current lighter linear overflow-alpha curve improves
  coverage; a small in-div core restores some colored-background ink, and the
  retained overflow-only one-row glyph write shift moves `site_0_google` to
  `2530` and current worst `site_44_the_new_york_times` to `3380`, while
  leaving the colored-background text compositing gap open.
  A later focused subpixel-only experiment improved in-div ink coverage but
  worsened `site_0_google` to `different_pixels: 2860` and SAD `575715`, so it
  remains rejected until the renderer can model Chrome's subpixel gamma,
  filtering, and colored-background compositing together.
  A calibrated colored-div threshold trial (`raw_alpha >= 160`, alpha `128`)
  was also rejected after regenerating `site_0_google`: it worsened the current
  oracle from `different_pixels: 2542` / `perceptual_pct_10000: 8892` to
  `different_pixels: 2572` / `perceptual_pct_10000: 8868`.
  Applying the current light alpha to every nonzero colored-div glyph pixel was
  rejected too: `site_0_google` worsened to `different_pixels: 2857` and
  `perceptual_pct_10000: 8672`.
  A direct full-glyph-alpha blend on colored backgrounds was also rejected:
  `site_0_google` worsened to `different_pixels: 2858` and SAD `543489`.
  A focused `raw_alpha >= 192` / alpha `96` trial on `site_15_twitch` was
  rejected because it raised colored-text SAD from `251059` to `251205` without
  improving actual ink coverage.
  A broader but lighter `raw_alpha >= 160` / alpha `32` trial on
  `site_15_twitch` improved actual colored-div ink from `150` to `213`, but it
  worsened colored-text SAD from `251059` to `251153` and full-screenshot
  differing pixels from `3151` to `3165`, so it remains rejected.
  A darker `raw_alpha >= 128` / alpha `160` trial improved actual colored-div
  ink further to `280`, but worsened colored-text SAD to `255993` and
  full-screenshot differing pixels to `3191`; stronger scalar darkening is
  therefore not sufficient on the real renderer-positioned pixels.
  A white-overflow alpha multiplier trial (`64 -> 72`) on `site_102_docker_hub`
  left exact differing pixels unchanged at `2955`, left measured overflow
  coverage unchanged at `1258/1608`, and slightly worsened perceptual score
  from `8645` to `8639`, so it is rejected.
  A blue-channel-only in-div darkening trial on `site_15_twitch` kept the same
  full-screenshot exact count (`3151`) and ink coverage (`150/1432`), but
  worsened colored-text SAD from `251059` to `251425`, so flat channel scaling
  is rejected too.
  The same analyzer reports Chrome has 5,444 chromatic non-white pixels while
  Simple still has 758 gray non-white text pixels, confirming the remaining
  gap is Chrome-style color/LCD coverage rather than only placement.
  It now also reports per-channel errors for the same sample:
  absolute RGB deltas `{r: 118580, g: 151826, b: 228663}` and signed
  actual-minus-expected deltas `{r: 101594, g: 135870, b: 212253}`, showing the
  dominant miss is in the blue channel.
  Region diagnostics split the failure into `1373` differing pixels inside the
  120x40 div box, with blue-channel absolute error `131501`, and `1144`
  differing pixels in the overflow text region on white, with near-balanced
  RGB absolute error around `95k-97k`; pixels below the text overflow are now
  identical.
  Line diagnostics from the Chrome text client rects show the first two lines
  on the blue div contribute `664` and `636` differing pixels with blue-channel
  dominated error, while overflow lines three and four contribute `756` and
  `373` differing pixels with balanced RGB error. Line-segment diagnostics now
  split each Chrome text rect at the div bottom:
  for `site_0_google`, line 3 is `27` differing pixels in-div versus `729`
  differing pixels in overflow; for current-worst
  `site_44_the_new_york_times`, line 5 is `0` in-div versus `402` overflow.
  This gives future text experiments a targeted gate for colored-background
  text versus white-background overflow coverage. Line three has the largest
  channel-sum error at `192445`.
  Per-line non-white extents now show lines 1 and 2 have identical expected and
  actual coverage boxes, so those failures are pure blue-background
  compositing. Overflow line 3 is `996` expected non-white pixels versus `819`
  actual, and line 4 is `302` expected versus `246` actual, so overflow-on-white
  text is under-covered rather than only shifted.
  The analyzer can now accept `chrome_metrics.json` and derives the div,
  overflow, and per-line regions from Chrome DOM rectangles instead of relying
  only on hardcoded `site_0_google` coordinates; the BDD diagnostic test uses
  that metrics-driven mode. It also reports per-region non-white coverage
  ratios: current `site_0_google` overflow text has `963` expected non-white
  pixels versus `751` actual (`actualPct10000: 7798`), and current
  `site_44_the_new_york_times` overflow text has `1608` expected versus `1253`
  actual (`actualPct10000: 7792`).
  The analyzer also reports dominant-background ink coverage, which exposes
  colored-box text omission that non-white coverage cannot see: current
  `site_0_google` has `1335` expected in-div ink pixels versus `259` actual.
  A darker grayscale calibration reduced total channel error to `498342` but
  worsened exact differing pixels to `2458`, so it is rejected for the current
  bitwise corpus gate.
  A stronger global darker-alpha calibration lowered SAD to `496035`, but
  worsened exact differing pixels to `2486` and perceptual score to `8903`; it
  was also rejected before the overflow-only fallback.
  A white-background-only raw-alpha blend improved overflow non-white coverage
  but worsened the exact diff to `2589` and SAD to `518121`, so scalar coverage
  strength is not sufficient without Chrome-compatible filtering/compositing.
  A smaller white-only curve lowered SAD to `498852`, but still worsened exact
  differing pixels to `2444`, so it is also rejected.
  A current PPM-only overflow intensity sweep showed that removing existing
  gray overflow text can improve exact counts on sampled pages while worsening
  SAD and deleting visible text. That false exact-count improvement is rejected
  and guarded by the corpus visible-overflow BDD.

Out of scope:

- Claiming full Chrome compatibility.
- Fetching or storing live third-party site HTML.
- Bitwise acceptance for text-antialiased live pages.

Tracked follow-up:

- `doc/bugs/simple_web_renderer_ttf_glyph_metrics.md` records the current TTF
  font parity blocker exposed by the wrapped `site_0_google` corpus
  comparison.
- `doc/bugs/engine2d_draw_text_bg_dispatch.md` records the resolved Engine2D
  `draw_text_bg` facade dispatch gap found while moving shared Engine2D text
  rendering toward `FontRenderer`.
