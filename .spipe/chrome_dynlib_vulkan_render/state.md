# Feature: Chrome Dynlib Vulkan Render Module

## Raw Request
build chrome rendering module with vulkan backed; make 2 showcases: chrome web rendering
showcase and simple webrenderer showcase which render almost all renderable HTML and CSS
elements (with tab-like screens). First setup chrome lib and chrome-backed vulkan showcase.
Research first and plan testing showcase infra. May use renderdoc. Chrome better to be in
dynlib.

## Task Type
feature

## Refined Goal
Load an embeddable Chromium (CEF) as a host-process shared library through the existing
SFFI dynlib facade, composite its offscreen frames through Engine2D onto Vulkan, and drive
the 4K lane's shared HTML/CSS catalog across its seven tabs to produce fail-closed PPM and
`key=value` receipt evidence comparable, apples-to-apples, with the Simple web renderer's
own receipts — without re-implementing the Simple showcase, the catalog, or GPU-offload infra.

## Acceptance Criteria
- AC-1: A pinned, digest-verified CEF-backed shared library exposes a frozen 10-symbol C ABI
  v1 and loads through the canonical host dynlib pattern (sha256-before, exact symbol set,
  sha256-after, `spl_dlclose`) with no symbol resolved outside the declared set.
- AC-2: The C boundary shim is justified by the absence of a host C->Simple trampoline, is
  `-fsyntax-only` clean, compiles on a host with no CEF present, and ships a Simple twin of
  its pure logic admitted by the dual-run shadow gate.
- AC-3: The chrome-backed showcase renders the identical `WebRenderableFeatureInventory`
  version and seven canonical tabs used by the Simple 4K lane, selecting tabs through real
  dispatched input rather than per-tab fixture files.
- AC-4: Every showcase run emits one PPM per tab plus a receipt carrying binary identity,
  library sha256, ABI and CEF versions, inventory version, viewport, reported backend,
  vulkan proof mode, wall seconds, frame p50/p95, max RSS, and pixel-diff status.
- AC-5: Verdicts are exactly `passed` / `failed` / `environment-blocked` /
  `could-not-complete-in-time`; a missing field, unresolvable binary, absent library, or
  zero-tab run is never `passed`, and Chrome availability alone is never Vulkan proof.
- AC-6: Perf and pairwise pixel comparison against the Simple lane use matching viewport,
  device scale, and inventory version, reuse the existing `perf_compare_admit_env`
  admission helper, and fail closed on incomplete tab coverage or tolerance violation.
- AC-7: Host-unavailable capability (CEF drop, CEF backend init, Chrome ANGLE Vulkan,
  RenderDoc) is recorded as an explicit blocked row with a resume command, never omitted
  and never inferred as a pass.
- AC-8: Every check script carries a fatal `--selftest` run before every scan, and a run
  that examined zero subjects is an error rather than a pass.

## Scope Exclusions
- The Simple-side all-HTML/CSS tabbed showcase, its inventory, and its tab semantics are
  owned by `.spipe/web_renderer_vulkan_4k_showcase_hardening` (AC-1..3) and are reused, not
  re-authored.
- GPU-offload infrastructure is owned by other agents.
- Zero-copy GPU handover (dma-buf / IOSurface external-memory import) is new runtime work
  and is deferred to a separate lane.
- Implementing currently unsupported HTML/CSS semantics.
- Release, version bump, and push are not requested.

## Runtime Boundary Decision
- runtime_need: Load an external third-party shared library in the host process, receive
  frame-ready callbacks from it, and upload the resulting BGRA image through the existing
  Engine2D Vulkan path.
- facade_checked: `DynLib.load` / `lib.sym` / `spl_wffi_call_i64` / `spl_dlclose` as used at
  `src/lib/nogc_sync_mut/gpu/chromium_reference_oracle_sffi.spl:236-287`; Engine2D's
  scaled-image upload at `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:176`; the 4K
  lane's shared fixture composer and inventory; `perf_compare_admit_env` in
  `scripts/check/check-chrome-simple-web-comparison.shs:168`.
- chosen_path: Reuse those facades unchanged. Add exactly one new C boundary file in
  `src/runtime/browser/` for the CEF callbacks, with a Simple twin for the dual-run gate,
  and a new Simple binding that copies the oracle load sequence verbatim.
- rt_used_in_s1: **ZERO new `rt_*` call sites outside the C shim.** The first draft copied
  the oracle binding's four (`rt_array_data_ptr_text`, `rt_byte_array_new_len`,
  `rt_ptr_read_i64`, `rt_bytes_to_text`); executing them proved the deployed seed does not
  back `rt_array_data_ptr_text` (`unknown extern function`), so the binding was rewritten
  onto the facade `spl_wffi_call_i64_with_bytes` (`dynlib_provider.spl:50`), which owns the
  buffer lifetime and length so Simple never holds C memory. The raw-pointer last-error
  reader was deleted rather than left uncallable (no unused code). The binding's directory
  `src/lib/nogc_sync_mut/gpu/` is in any case an allowlisted provider prefix
  (`scripts/check/no_direct_rt_allowlist.txt:88`), so the `push-no-direct-rt` ratchet count
  is unchanged either way.
- rejected_shortcuts: No raw `dlopen` outside the facade; no Simple-side ownership of C
  memory (all buffer returns use the `*_into(buf, cap, out_len)` idiom); no second catalog
  generator; no Electron or headless-screenshot capture substituted for embedded-library
  evidence; no Chrome availability promoted as Vulkan proof; no zero-copy claim without a
  real external-memory import; no Rust-seed fallback.

## Research Summary
- A "chrome dynlib" already exists and is a **broker, not an embed**:
  `tools/chromium-primitive-oracle/` builds `libsimple_chromium_primitive_oracle` but spawns
  a pinned Electron 42.5.0 / Chrome 148.0.7778.271 and returns a CPU `capturePage`.
- Chrome is launched two ways today, neither embedded: that Electron broker, and headless
  process spawn at `test/05_perf/web_render_chrome/chrome_runner.spl:30-86`
  (`--headless=new --screenshot=<png> file://<html>`).
- The prior `chrome-class-browser-plan` lane (CLOSED 2026-05-20) shipped only a 35-line
  roadmap doc (`ef320825a97`) — no code to reuse.
- CEF is the recommended library: the only candidate that is real Chromium, a genuine
  shared library, and capable of accelerated offscreen output. All external CEF facts are
  UNVERIFIED (no network in this sandbox).
- Engine2D Vulkan accepts images only as `pixels: [u32]`; no external-memory import exists,
  so v1 is necessarily a CPU BGRA round trip.
- No host C->Simple trampoline exists (`grep trampoline` over `src/runtime` and
  `src/lib/nogc_sync_mut/ffi` finds only a baremetal file), which is what forces the C shim.
- Vulkan proof vocabulary is already fixed by
  `doc/07_guide/tooling/renderdoc_capture_infra.md:748-790`
  (`gui_web_2d_vulkan_*`, `vulkan-angle-unavailable`, `rdoc_capture_status=unavailable`).
- Host state verified 2026-09-11: `renderdoccmd` absent.

## Phase
s3-complete (S1 shim/twin/binding/probe + S2 catalog/composite/receipt + S3 perf check
landed; every Chrome-backed row is honestly `environment-blocked` — no CEF drop on this
host. Boundary respected: the Simple-side showcase is untouched beyond writing the SHARED
catalog it consumes.)

## Log
- research: Audited the closed chrome-class lane, the chromium primitive oracle dylib and
  its SFFI load sequence, both existing Chrome launch paths, the Engine2D Vulkan image
  entry points, the C-callback gap, and the existing receipt/Vulkan-proof key vocabulary.
  Produced `doc/01_research/ui/chrome_dynlib/chrome_dynlib_vulkan_render_module_2026-09-11.md`
  and its TL;DR.
- plan: Produced `doc/03_plan/ui/chrome_dynlib/chrome_dynlib_vulkan_showcase_plan.md` with
  slices S1 (shim + binding + probe), S2 (chrome-backed Vulkan showcase), S3 (perf +
  comparison), and five explicit blocked rows (B1 CEF drop, B2 backend init, B3 ANGLE
  Vulkan on macOS, B4 RenderDoc, B5 zero-copy) each with a Linux resume command.
- blocked: No network in this agent's sandbox, so every external CEF claim is marked
  UNVERIFIED and must be re-checked against cef-builds before S1 lands.
- s1 (2026-09-11, macOS arm64): Implemented the C shim (`src/runtime/browser/
  chrome_render_shim.{c,h}`, exactly 10 exported symbols, `-fvisibility=hidden`, all CEF
  includes behind `SIMPLE_CHROME_CEF`, `clang -fsyntax-only -Wall -Wextra` clean), its
  Simple twin (`src/lib/common/browser/chrome_render_shim_twin.spl`), the binding
  (`src/lib/nogc_sync_mut/gpu/chrome_render_module_sffi.spl`, oracle load sequence copied
  verbatim and extended to NAME the unresolved symbol), the build script
  (`scripts/check/build-chrome-render-shim.shs`, `nm` exact-set assertion + `.sha256`
  sidecar), the two-stage probe (`scripts/check/check-chrome-dynlib-probe.shs`, 5 fatal
  selftest fixtures), and the spec (11 examples, 0 failures).
  Evidence: `CHROME_DYNLIB PROBE: ALL PASS — 10/10 symbols, abi=1,
  lib_sha256=fe87e9e117de24ac98d292d1d46e46e83b5ad6820d399fda946bbf3f8e9d986e,
  backend_stage=blocked:no-cef-drop`.
  Sabotage (green/red/green): renaming `simple_chrome_render_event` out of a built copy
  makes the probe report `FAIL — symbol-missing, missing symbol:
  simple_chrome_render_event` (exit 1); the unmodified library passes on both sides.
- s1-setup (scope addition): `scripts/setup/setup-cef-dynlib.shs` is now a real cross-OS
  setup (`--check` / `--install` / `--env` / `--selftest`, 5 fatal fixtures) with a native
  PowerShell twin `scripts/setup/setup-cef-dynlib.ps1`, both reading ONE pin file
  `config/cef/cef_pin.sdn`. `--install` is fail-closed on an `UNSET` digest unless
  `--allow-unpinned`, which is announced loudly and still records
  `cef_sha256_status=unpinned`. Measured on this Mac: `--selftest` 5/5;
  `--check` -> `cef_platform=macosarm64 ... cef_reason=no-cef-drop cef_status=missing`
  (exit 1), `macos_helper_status=required-unverified-from-non-bundled-cli`.
  Guide: `doc/07_guide/app/ui/chrome_dynlib_setup.md`.
- s1-stageB-exercised: `--require-backend` against the STUB build drives the real
  `create()` call path end to end and prints
  `CHROME_DYNLIB PROBE: FAIL — --require-backend but backend_stage=blocked:backend-unavailable`
  (exit 1). That is the shim honestly refusing, and it proves the stage-B marshalling works
  for the Linux resume row rather than being untested code. Stage A additionally calls
  `destroy(0)` and asserts it returns 2 — a resolved symbol is not a callable one.
- s1-open: the Simple twin is **not** admitted by `check-dual-run-shadow.shs`. That gate
  discovers pairs only from `# @dual_pair: ... ref=<rt_*> cand=<std...>` spec annotations
  (`enumerate_pairs`, :47) and its `ref=` side must be a callable `rt_*`; the C
  counterparts are deliberately `static` inside the shim, so no such annotation can be
  written without widening the frozen 10-symbol ABI. AC-2's twin half is therefore written
  but unproven by that gate; resolve before closing the lane.
- blocked (S1 stage B, unchanged): no CEF drop on this host and no network to stage one, so
  `create()` was never called against a real backend. Every pin value in
  `config/cef/cef_pin.sdn` is a placeholder and is UNVERIFIED.

- s2-landed (2026-09-11): `src/app/ui/chrome_showcase/{catalog,frame,receipt,main}.spl`.
  The shared catalog is SLICED from the 4K lane's own composed fixture — 7 canonical panel
  pages (overview, html, css-layout, css-paint, forms-media, animation, evidence) plus a
  `tab-bar` page — into `examples/06_io/ui/web_catalog/*.html` with a `catalog.sdn` index,
  so the Simple web renderer showcase consumes byte-identical input. No second inventory or
  generator was authored. Frames composite through Engine2D
  (`create_with_backend_fast` -> `draw_image` -> `read_pixels`) and are written as binary P6
  PPMs alongside `build/chrome-showcase/receipt.env`. Measured (deployed binary size
  26264696, mtime 1788766698, interpreter): `cpu_simd`->`cpu_simd` 8 tabs 14691 ms;
  `vulkan`->`vulkan` (real Vulkan, Apple M4) 8 tabs 22613 ms; both
  `frame_source=stub-pattern reason=no-cef-drop verdict=environment-blocked`.
- s3-landed (2026-09-11): `scripts/check/check-chrome-web-showcase-perf.shs`. Runs both
  backends, classifies both receipts, prints the `chrome_web_showcase_*` aggregates.
  Verdict here: `PASS — 16 tab(s) checked across 2 backend(s), status=blocked
  frame_source=stub-pattern reason=no-cef-drop`. `--selftest` 6/6 fatal fixtures.
  `chrome_vs_simple_pixel_diff_status=unavailable` (peer PPM dir
  `build/web_renderer_vulkan_4k_showcase_hardening/simple/ppm` absent);
  `renderdoc_status=blocked:renderdoccmd-missing` under `--renderdoc`.
- specs: `test/01_unit/app/ui/chrome_web_showcase_receipt_spec.spl` 17 examples 0 failures;
  `..._catalog_spec.spl` 10 examples 0 failures. Sabotage triple: making
  `chrome_showcase_verdict_of_body` trust the body's own `verdict=` line instead of
  re-deriving it gives 16/17 (the "receipt that lost frame_source" example goes red);
  restored -> 17/17.

## RUNTIME NEED (recorded, per the no-new-rt_* rule)

- **Bounded OUT-byte-buffer dynlib call.** `simple_chrome_render_read_pixels_into(h, buf,
  cap, out_len)` writes into a caller-owned buffer. The host facade
  (`src/lib/nogc_sync_mut/sffi/dynamic.spl`) exposes only `spl_wffi_call_i64`,
  `spl_wffi_call_i64_checked`, `spl_wffi_try_call_i64_out` (one `*mut i64`) and, in the
  chrome binding, `spl_wffi_call_i64_with_bytes` — which passes bytes **IN** only. There is
  no way to hand the provider a byte buffer to fill. A real Chrome frame therefore cannot
  be pulled until a `spl_wffi_call_i64_into_bytes(fptr, prefix_args, out_bytes, offset,
  capacity, suffix_args) -> i64` facade exists. **This is a facade addition, not a new
  `rt_*`**, and S2 introduced no new `rt_*` anywhere. Until it lands, the composited frame
  is the twin's deterministic test pattern, stamped `frame_source=stub-pattern`.

## OPEN AGAINST THE ACs

- **AC-3 (real dispatched input) is UNMET.** Tabs are selected by per-tab catalog PAGE, not
  by dispatching a click through `simple_chrome_render_event`. Honest reason: there is no
  backend on this host to dispatch into. The event symbol is resolved and frozen in the
  ABI; wiring the dispatch belongs with the first real CEF drop.
- **AC-4 perf rows are partial.** Wall time per tab is recorded; cold first-frame, warm
  p50/p95 and max RSS are not, and `perf_compare_admit_env` is not yet reused. With
  `frame_source=stub-pattern` those would be percentiles of a test pattern, so they were
  deliberately left out rather than filled with meaningless numbers.
- **CEF pin reworked (2026-09-11).** `config/cef/cef_pin.sdn` no longer carries a
  hand-maintained per-platform sha256 table (all six rows were `UNSET`, so every install
  needed `--allow-unpinned` and nothing was verified). The pin is now the VERSION LINE
  (`143.0.13`, matched as a prefix on the index's `cef_version`); `--install` resolves the
  archive and its `sha1` from `https://cef-builds.spotifycdn.com/index.json`, admits the
  download against that publisher digest (printed as `cef_index_sha1=`), then records the
  measured sha256 at `build/cef/<version>/<platform>/admitted.sha256`, which is what
  `--check` verifies against. A drop with no such record is `unadmitted` and reports
  `missing`, never `present`. `--allow-unpinned` now means "a version NOT in the index"
  (a locally built drop). `.ps1` twin updated identically via `ConvertFrom-Json`.
  `--selftest` is 9/9 (4 new fixtures prove the index parser offline: correct resolve, the
  platform axis really discriminates, an absent version resolves to NOTHING, sha1
  verification discriminates). **UNVERIFIED:** the version string `143.0.13` and the index
  shape were not read from the network — this sandbox has none. `--install` was NOT run.
- **filed:** `doc/08_tracking/bug/indexed_field_assignment_unsupported_2026-09-11.md` —
  `receipt.rows[3].nonblank = false` is refused with "complex indexed field receiver is not
  supported", forcing a full struct rebuild in a test fixture.

## Review pass (same session, 2026-09-11) — three real holes closed

- **A stub receipt claiming `verdict=passed` was accepted as a pass.** Both classifiers
  checked `frame_source` validity and `verdict` validity independently, so hand-editing one
  key in a blocked receipt laundered a synthetic test pattern into a claimed Chrome pass —
  the exact invariant `frame_source` exists to protect. Now `frame_source=stub-pattern` +
  `verdict=passed` is `failed` in `chrome_showcase_verdict_of_body` and
  `stub-pattern-claims-passed` in the shell classifier. The existing fixtures all used
  `frame_source=chrome`, which is why none of them caught it. Perf selftest 6 -> 7 fixtures;
  receipt spec 17 -> 18 examples.
- **The showcase never invoked the binding.** It only did `file_exists` on the library path
  and HARDCODED `backend_stage`, leaving `chrome_lib_sha256=` empty. It now builds nothing
  by itself but, when `build/chrome-render/libsimple_chrome_render.dylib` is present, runs
  the real `chrome_render_load` (sha256 -> `DynLib.load` -> exact 10-symbol resolution ->
  sha256 again) and the real `chrome_render_create`, and records the MEASURED
  `chrome_render_backend_stage(created)` plus the real digest. Against the stub shim built
  by `scripts/check/build-chrome-render-shim.shs` this reports
  `chrome_lib_sha256=6a9ad5f5324a947a318d1accfdb0293ec6c0db962b93f2196019b1a6a786b112`,
  `backend_stage=blocked:backend-unavailable`,
  `reason=no-cef-drop:blocked:backend-unavailable` — the shim honestly refusing, not a
  string this program chose. Correction to the note above: `read_pixels_into` is not the
  only unreached symbol; `load_html` / `resize` / `render_frame` / `event` are also not yet
  driven (they are expressible today — only the readback needs the new facade).
- **`catalog_sha256` claimed to bind the pages and hashed only `catalog.sdn`.** Each page's
  own sha256 is now recorded as a `sha256:` row in `catalog.sdn`, so a digest of that one
  file transitively covers every page byte; an index row with an empty digest is rejected by
  `chrome_catalog_index_consistent`.
- Also: `chrome_vs_simple_pixel_mismatch_count` now counts differing PIXELS (`cmp -l` byte
  lines / 3 for P6) rather than differing files; the unused `chrome_frame_checksum` helper
  was deleted (no-unused-code rule).

Seed run, as requested (`src/compiler_rust/target/bootstrap/simple`, size 130402384, mtime
1788606093): `cpu_simd` -> `engine2d_backend_reported=cpu_simd`, 8 tabs, 14365 ms,
`verdict=environment-blocked`.
