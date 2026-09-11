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
s1-complete (shim + twin + binding + probe + CEF setup landed; S2/S3 not started)

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
