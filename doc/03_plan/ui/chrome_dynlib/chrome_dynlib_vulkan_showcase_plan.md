# Plan — Chrome Dynlib + Vulkan-Backed Showcase Infra

Research: `doc/01_research/ui/chrome_dynlib/chrome_dynlib_vulkan_render_module_2026-09-11.md`.
Scope boundary (user-set): stop after the chrome showcase infra + perf check. The Simple-side
all-HTML/CSS tabbed showcase is owned by `.spipe/web_renderer_vulkan_4k_showcase_hardening`
(AC-1..3); GPU-offload infra is owned by other lanes. Neither is re-implemented here.

Every slice is sized for one Opus/Sonnet agent, ≤1 day. Every verification command must
print its evidence line as the **last line of stdout**. Verdicts are fail-closed and exactly
four: `passed` / `failed` / `environment-blocked` / `could-not-complete-in-time`.

---

## S1 — Dynlib shim, Simple binding, and load probe

**Status:** DONE 2026-09-11 (macOS arm64). Stage A green; stage B honestly
`blocked:no-cef-drop` — this host has no pinned CEF drop and no network to stage one.
Evidence: `CHROME_DYNLIB PROBE: ALL PASS — 10/10 symbols, abi=1,
lib_sha256=fe87e9e117de24ac98d292d1d46e46e83b5ad6820d399fda946bbf3f8e9d986e,
backend_stage=blocked:no-cef-drop` (probe selftest 5/5 fatal fixtures; spec 11 examples,
0 failures; sabotage — one export renamed away — gives `FAIL — symbol-missing, missing
symbol: simple_chrome_render_event`).
Additional files landed beyond the list below (user scope addition): a real cross-OS CEF
setup (`scripts/setup/setup-cef-dynlib.shs` + `.ps1` twin) driven by one pin file
`config/cef/cef_pin.sdn`, documented at `doc/07_guide/app/ui/chrome_dynlib_setup.md`.
The build script and probe consume `SIMPLE_CEF_ROOT` from its `--env` output, so a host
with a drop builds the real shim (`-DSIMPLE_CHROME_CEF`) and a host without builds the stub.

Files to create:
- `src/runtime/browser/chrome_render_shim.c` + `.h` + `FILE.md` — `src/runtime/browser/` does
  not exist yet, so the directory manifest is part of this slice (structure.md, enforced by
  `scripts/check-workspace-root-guard.shs`). CEF ABI v1, the 10 `simple_chrome_render_*`
  symbols from research §3.2. This ABI is a **sibling of, not a replacement for**, the frozen
  5-symbol `simple_chromium_oracle_*` ABI
  (`doc/08_tracking/bug/chromium_oracle_canonical_admission_plan_2026-09-08.md:55-72`): disjoint
  prefix, same `nm -gU` exact-set discipline, and the oracle's detail design explicitly disclaims
  ownership of production Chrome wrappers and Engine2D
  (`doc/05_design/chromium_web_renderer_primitive_differential.md:65-70`), so there is no overlap
  to resolve. Owns the `cef_render_handler_t` callbacks because the repo FFI
  calls forward only. Must be `-fsyntax-only` clean (blocking push gate) and must not
  `#include` CEF headers unguarded — wrap in `SIMPLE_CHROME_CEF` so the stub build compiles
  on a host with no CEF and returns `CHROME_RENDER_E_BACKEND_UNAVAILABLE`.
- `src/lib/common/browser/chrome_render_shim_twin.spl` — Simple twin of the shim's pure logic
  (frame state machine, buffer-bounds validation, error-code mapping) for the dual-run gate.
- `src/lib/nogc_sync_mut/gpu/chrome_render_module_sffi.spl` — binding, copying
  `chromium_reference_oracle_sffi.spl:236-287` (digest-before / `DynLib.load` / exact symbol
  set / digest-after / `spl_wffi_call_i64` / `spl_dlclose`, all `@unsafe(capabilities:[ffi,raw_ptr])`).
- `scripts/check/build-chrome-render-shim.shs` — build to
  `build/chrome-render/libsimple_chrome_render.{dylib,so}`, emit a `.sha256` sidecar, and
  assert the exported symbol set is **exactly** the 10 names (model:
  `scripts/check/build-chromium-primitive-oracle.shs:339-353`).
- `scripts/check/check-chrome-dynlib-probe.shs` — two-stage probe. Stage A: build, digest,
  `DynLib.load`, resolve all 10, assert `abi_version()==1`, `destroy`, `spl_dlclose`.
  Stage B: `create()` against a real CEF backend. Stage B recorded as a field, never as a
  silent skip. `--selftest` fatal (≥4 fixtures: clean PASS; one missing symbol FAILs naming
  it; digest mismatch FAILs; no-library ERRORs — a 0-symbol probe is never a pass).
- `test/01_unit/lib/nogc_sync_mut/gpu/chrome_render_module_sffi_spec.spl`

Verify: `sh scripts/check/check-chrome-dynlib-probe.shs`
Evidence line: `CHROME_DYNLIB PROBE: ALL PASS — 10/10 symbols, abi=1, lib_sha256=<d>, backend_stage=<ok|blocked:<reason>>`

---

## S2 — Chrome-backed Vulkan showcase (catalog, tabs, PPM + receipt)

**Status:** DONE 2026-09-11 (macOS arm64), `environment-blocked` as the honest verdict.
Vulkan **proof** rows remain host-blocked (row B3); the Engine2D Vulkan *path* is real.

**Filenames differ from the list below — the user's S2/S3 brief renamed them, and those
names are what shipped.** The entry kept the plan's name; the rest follow the brief:
`src/app/ui/chrome_showcase/main.spl` (entry, as planned) plus three pure siblings
`catalog.spl` / `frame.spl` / `receipt.spl`; the catalog lands at
`examples/06_io/ui/web_catalog/*.html` + `catalog.sdn`; the receipt is
`build/chrome-showcase/receipt.env`. The separate
`check-chrome-dynlib-showcase-receipt.shs` was NOT written — its receipt-reading duty is
performed by S3's single script, which reads the same receipt and would otherwise be a
second copy of the same classifier.

Catalog provenance: the pages are SLICED out of the 4K lane's own composed document
(`web_renderable_feature_inventory_apply_to_showcase` over
`examples/06_io/ui/browser_common_elements_showcase.html`), one page per canonical panel
(7: overview, html, css-layout, css-paint, forms-media, animation, evidence) plus a
`tab-bar` page = 8. No second inventory and no second generator was authored.

Measured on this Mac (deployed binary size 26264696, mtime 1788766698, interpreter):
`cpu_simd` reported `cpu_simd`, 8 tabs, 14691 ms; `vulkan` reported `vulkan` (real Vulkan
on Apple M4), 8 tabs, 22613 ms. Both: `frame_source=stub-pattern reason=no-cef-drop
verdict=environment-blocked`, 8 non-blank PPMs each.

**Two honest gaps, recorded not worked around.** (1) Tab selection is by per-tab catalog
PAGE, not by a dispatched `simple_chrome_render_event` click — AC-3's "real dispatched
input" is unmet and stays open, because no backend exists on this host to dispatch into.
(2) `simple_chrome_render_read_pixels_into` writes into a caller-owned OUT buffer and the
host dynlib facade has no bounded out-byte-buffer call (`spl_wffi_call_i64_with_bytes`
passes bytes IN only), so a real Chrome frame cannot be pulled yet; that needs a facade
addition (`spl_wffi_call_i64_into_bytes`), not a new `rt_*`. Both are in the lane state.

Original file list (superseded by the names above, retained for provenance):
- `src/app/ui/chrome_showcase/main.spl` — loads the shared catalog via the 4K lane's
  `src/lib/gc_async_mut/gpu/browser_engine/web_renderable_feature_inventory.spl` and its
  shared fixture composer (present in this worktree; reuse — do **not** author a second
  generator). That lane is `implementation-active`, so S2 must assert the inventory module
  and its version field resolve before rendering and record
  `chrome_dynlib_inventory_version`; if the module is absent on the branch being built,
  the run is `environment-blocked` with `reason=inventory-not-landed`, never a synthesized
  substitute catalog. Drives the seven canonical tabs by dispatching a click through
  `simple_chrome_render_event`, pulls each frame via `render_frame` + `read_pixels_into`,
  uploads through Engine2D's existing `pixels: [u32]` scaled-image path
  (`engine2d/backend_vulkan.spl:176`), presents on Vulkan, writes one PPM per tab plus a
  `receipt.env`.
- `scripts/check/check-chrome-dynlib-showcase-receipt.shs` — fail-closed receipt wrapper
  modelled on `scripts/check/check-web-showcase-4k-receipt.shs`; binds deployed-binary
  identity (`readlink -f` + size + mtime per `.claude/rules/commands.md`), library SHA-256,
  inventory version, viewport, and all `chrome_dynlib_*` fields from research §4.
- `test/03_system/app/ui.browser/feature/chrome_dynlib_showcase_spec.spl`

Verify: `sh scripts/check/check-chrome-dynlib-showcase-receipt.shs --viewport 3840x2160`
Evidence line: `CHROME_DYNLIB SHOWCASE: chrome_dynlib_status=<verdict> tabs=7/7 ppm_written=7 vulkan_proof_mode=<mode> reason=<r>`

---

## S3 — Perf check + Simple↔Chrome comparison contract

**Status:** DONE 2026-09-11. Comparison admission is fail-closed and currently
`unavailable` — the Simple side has produced no PPMs for this catalog yet.

Shipped as ONE script, `scripts/check/check-chrome-web-showcase-perf.shs` (the brief's
name), which subsumes both planned scripts: it runs the showcase for `cpu_simd` and
`vulkan`, reads each receipt, and prints `chrome_web_showcase_{status,_reason,
_frame_source,_backend_reported,_tabs,_wall_ms_total,_ms_per_px}` plus
`chrome_vs_simple_pixel_diff_status` / `_mismatch_count` in the `gui_web_2d_vulkan_*`
naming discipline of `check-electron-vulkan-web-parity.shs`. Fatal `--selftest`: 6 fixtures
(good receipt PASS, missing receipt ERROR, `verdict=failed` FAIL, 0 tabs ERROR, receipt
with no `frame_source` FAIL, `environment-blocked` classified blocked with its reason).

Verdict on this Mac: `PASS — 16 tab(s) checked across 2 backend(s), status=blocked
frame_source=stub-pattern reason=no-cef-drop`, with
`chrome_vs_simple_pixel_diff_status=unavailable` (documented peer path
`build/web_renderer_vulkan_4k_showcase_hardening/simple/ppm`, overridable with
`SIMPLE_WEB_SHOWCASE_PPM_DIR`, does not exist here) and
`renderdoc_status=blocked:renderdoccmd-missing` under `--renderdoc` (row B4 — recorded,
never a silent skip).

**Not shipped:** `perf_compare_admit_env` reuse and the cold/warm p50/p95 + max-RSS rows.
The current script measures per-tab wall time only, because with `frame_source=stub-pattern`
a frame-time percentile would be a percentile of the test pattern, not of Chrome. Those
rows belong with the first real backend and stay open.

Original file list (superseded, retained for provenance):
- `scripts/check/check-chrome-dynlib-perf.shs` — cold first-complete-frame and warm
  p50/p95 per tab, max RSS, wall seconds; emits every `chrome_dynlib_*` field. Reuses the
  `perf_compare_admit_env` admission helper (defined in
  `scripts/check/lib/perf-comparison-admission.shs`, called at
  `scripts/check/check-chrome-simple-web-comparison.shs:168`), so ratio rows are
  `admitted` / `skipped` with an explicit `_reason` and never a bare number.
- `scripts/check/check-chrome-dynlib-vs-simple.shs` — pairwise per-tab pixel diff at matching
  viewport and device scale against the 4K lane's Simple receipt; documented tolerance;
  `chrome_dynlib_pixel_diff_status` + `chrome_dynlib_pixel_mismatch_count`. Fails closed on
  missing captures, mismatched inventory version, or incomplete tab coverage.
- `test/05_perf/web_render_chrome/chrome_dynlib_runner.spl`

Both scripts carry a fatal `--selftest` (clean PASS; missing-field FAIL; zero-tab run ERROR;
mismatched-inventory FAIL). Chrome availability alone is **never** Vulkan proof.

Verify: `sh scripts/check/check-chrome-dynlib-perf.shs --selftest && sh scripts/check/check-chrome-dynlib-perf.shs`
Evidence line: `CHROME_DYNLIB PERF: status=<verdict> wall_s=<w> frame_ms_p50=<a> frame_ms_p95=<b> rss_mb=<r> compare=<admitted|skipped:<reason>>`

---

## Blocked rows — recorded, never omitted

| id | subject | why blocked on this host | resume command (Linux) |
|---|---|---|---|
| B1 | CEF binary drop | no network in this sandbox (curl/wget/WebFetch blocked); the pinned `.tar.bz2` + SHA-256 must be staged out-of-band exactly as the Electron broker pin is | stage the pinned CEF drop, then `sh scripts/check/build-chrome-render-shim.shs --cef-root <dir>` |
| B2 | S1 stage B (`create()` on a real backend) | depends on B1; CEF macOS also needs a helper `.app` for its subprocesses, feasibility under `dlopen` from a non-bundled CLI is UNVERIFIED | `sh scripts/check/check-chrome-dynlib-probe.shs --require-backend` |
| B3 | Chrome ANGLE-Vulkan proof | macOS ANGLE backs onto Metal; per `doc/07_guide/tooling/renderdoc_capture_infra.md:748` this host records `vulkan-angle-unavailable` and the browser Vulkan gate stays failed | on Linux: `sh scripts/check/check-chrome-dynlib-showcase-receipt.shs --require-vulkan-proof` |
| B4 | RenderDoc capture | `command -v renderdoccmd` -> not found (verified 2026-09-11); rows are `rdoc_capture_status=unavailable`, `rdoc_capture_reason=missing-renderdoc` | `renderdoc-evidence.shs` takes subcommands (`env\|capture-simple\|capture-html\|capture-electron-html`, usage at `:44`) and has no chrome-dynlib scene, so the resume step is: add a `capture-chrome-dynlib` subcommand, then on a Linux host with RenderDoc run `sh scripts/tool/renderdoc-evidence.shs capture-chrome-dynlib` |
| B5 | Zero-copy GPU handover | Engine2D has no external-memory import; needs new `rt_*` surface + `VK_EXT_external_memory_dma_buf` (Linux) / MoltenVK IOSurface (macOS) | out of scope for S1-S3; file as a separate lane before attempting |

## Explicitly out of scope
- The Simple-side all-HTML/CSS tabbed showcase and its inventory (owned by the 4K lane, AC-1..3).
- GPU-offload infrastructure (owned by other agents).
- Implementing unsupported HTML/CSS semantics.
- Any zero-copy GPU path (B5).
- Release, version bump, or push.
