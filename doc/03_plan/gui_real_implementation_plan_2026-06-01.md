# Real Pure Simple GUI Implementation Plan - 2026-06-01

<!-- codex-design -->

## Objective

Implement the real macOS host GUI path as a pure Simple GUI library loaded from
the pure SMF dynlib artifact by default, with hot event response below 1 ms on
the macOS arm64 host profile. On macOS, the host adapter uses SFFI dynload to
open and call the dynlib extracted from that SMF artifact. The SimpleOS QEMU
ARM64 lane must use the same pure SMF dynlib artifact through a
framebuffer/virtio presentation adapter.

This plan replaces the earlier hosted WM and Simple Web Renderer direction.
Those paths remain smoke/regression coverage only and are not release evidence
for this goal.

## Notice: Pure Simple Constraint

This plan must be implemented in pure Simple wherever the repository can express
the behavior in `.spl`. Do not add new Rust runtime `rt_*` externs, Rust SFFI
helpers, or Rust-hosted GUI logic to satisfy this goal. If a native escape hatch
is unavoidable after the Simple path is proven insufficient, implement the
smallest possible C bridge rather than Rust, and keep it outside the measured
GUI library logic.

The 2D engine should also prefer pure Simple. Any C fallback for platform or
pixel-adjacent primitives must preserve existing rendering pixel logic and must
not change raster output, glyph metrics, colors, placement, or comparison
thresholds.

## Target Stack

```text
pure Simple GUI library
  -> SMF artifact
  -> pure SMF dynlib default
  -> macOS arm64 SFFI dynload adapter / SimpleOS SMF loader
  -> stable GUI command ABI
  -> platform adapter presentation
```

The GUI library owns widget state, event routing, focus, invalidation, layout
metadata, and render command emission. Platform adapters own only native event
collection, dynlib/SMF loading, clocks, and final presentation.

## Explicitly Removed From The Release Path

- `rt_gui_*`, `rt_winit_*`, `rt_sdl_*`, `rt_cocoa_*`, and related native GUI
  runtime calls inside WM, GUI library, and web renderer modules.
- `HostCompositor` as acceptance evidence for the macOS path.
- `SimpleWebRenderer`, HTML layout, browser surfaces, and `WebRenderRequest` as
  the GUI app content path.
- Direct framebuffer or demo WM programs as proof of the requested GUI library.

Adapters may still call native presentation/runtime functions after the pure
Simple GUI library has returned command batches. Those adapter calls must not be
part of the measured sub-1 ms library response unless explicitly separated in
the evidence.

## Performance Contract

- Hot response metric: event ingress to updated GUI command batch emitted from
  the loaded SMF/dynlib library.
- Required threshold: p99 < 1000 us after warmup on macOS arm64.
- Required reporting: p50, p95, p99, max, iteration count, warmup count, host
  CPU/OS, artifact path, loader mode, and whether the result came from dynlib,
  interpreter, JIT, or fallback.
- Excluded from the hot metric: cold SMF load, dynlib open, QEMU boot, screenshot
  capture, final platform present, and pixel diffing.
- Rendering pixel logic is frozen. Do not optimize by changing raster output,
  blending, glyph, color, layout pixel placement, or compare thresholds.

## Current Findings

- SMF and dynlib support exists in `src/os/smf/`, `src/os/kernel/loader/`,
  `src/compiler/99.loader/`, and `src/os/posix/dynlib.spl`.
- `src/lib/gui/pure_core.spl` provides the pure GUI event/update/render command
  ABI without WM, Simple Web, or native GUI runtime imports.
- `src/lib/gui/pure_smf_dynlib_perf.spl` provides the SMF/dynlib perf report
  contract and rejects fallback, unresolved symbols, non-dynlib runs, and p99
  values at or above 1000 us.
- `src/app/gui_perf/smf_dynlib_probe.spl` is the CLI evidence probe. It emits a
  `GUI_DYNLIB_PERF` row and fails closed for direct Simple fallback samples
  until runtime dynlib symbol invocation is real.
- `src/app/gui_perf/macos_smf_dynlib_release_gate.spl` is the macOS acceptance
  command. It runs the evidence chain, writes a transcript, validates the full
  ordered SMF artifact, QEMU parity, SimpleOS dynload parity, mac dynlib perf,
  and mac pass rows, and fails closed unless the transcript proves the real SMF
  dynlib hot-call path.
- `src/app/gui_perf/linux_smf_dynlib_e2e_gate.spl` and
  `test/system/gui/linux_smf_dynlib_e2e_gate_system_spec.spl` provide the
  repeatable Linux evidence lane. The gate builds the pure GUI hot dynlib,
  wraps it into `build/gui/pure_gui_hot.smf`, probes the extracted payload
  through SFFI, and requires `loader=smf_dynlib`, `dynload=smf_dynlib`,
  `host_dynload=sffi`, `call_source=dynlib_symbol_call`, and `pass=true`.
  This does not replace the macOS arm64 evidence requirement, but it prevents
  regressions back to raw host dynlib or direct Simple fallback while mac
  hardware evidence is pending.
- `src/app/gui_perf/pure_gui_hot_dynlib_export.spl` provides a pure Simple,
  i64-only exported hot symbol that can be built as a host `.so`/`.dylib` for
  callable ABI diagnostics. This proves dynlib call overhead separately, but
  `loader=host_dynlib` remains non-acceptance evidence for the SMF goal.
- Do not solve the remaining SMF/dynlib gap by adding Rust runtime helpers.
  Prefer pure Simple SMF envelope, symbol, and probe code. If direct native
  symbol invocation cannot be expressed in Simple, use a minimal C bridge at the
  adapter boundary and keep the GUI library pure Simple.
- Existing WM and hosted examples still contain direct `rt_gui_*` and
  `rt_winit_*` extern calls. They must not be imported by the release lane.
- Existing Simple Web renderer files are renderer/browser feature code, not the
  requested pure Simple GUI library.
- Existing QEMU capture and WM tests prove presentation or screenshots, not
  sub-1 ms GUI library response from an SMF/dynlib artifact.

## Architecture Decisions

- Keep the pure GUI library independent from WM, Simple Web, and hosted runtime
  modules.
- Use a narrow ABI made of value records: event batch in, command batch out,
  dirty region summary, and timing counters.
- Cache symbol settlement and function handles once per loaded artifact.
- Reuse preallocated event, command, and dirty-region buffers across hot
  iterations.
- Use dirty-region metadata and command batching for performance. Pixel
  generation behavior must remain byte-for-byte compatible with the pre-existing
  renderer for any covered scene.
- Treat QEMU ARM64 as artifact portability evidence. Its performance target is
  reported separately unless the user later selects a strict QEMU NFR.

## Renderer And Shell Comparison

This comparison decides what can be release evidence for the real GUI
implementation and what remains renderer, browser, or shell compatibility
coverage.

### CPU-Backed 2D Versus Vulkan-Backed 2D

CPU/software Engine2D remains the canonical deterministic pixel reference:
`doc/06_spec/integration/rendering/engine2d_backend_spec.md` and
`doc/06_spec/integration/rendering/backend_screenshot_compare_spec.md` cover
exact screenshot comparison. Vulkan Engine2D remains an accelerated
presentation candidate only after parity evidence such as
`doc/06_spec/integration/rendering/engine2d_cpu_vulkan_parity_spec.md` and
`doc/09_report/vulkan_engine2d_readback_2026-05-31.md` proves zero mismatches
and no blur/tolerance use. Vulkan must not be used to hide GUI-library latency;
the hot metric stays event ingress to SMF/dynlib command-batch emission.

### Web Rendering Library With Node.js

Node.js is useful as a repeatable JavaScript bitmap baseline, but it is not the
real GUI implementation target. The current Node.js Engine2D lane
(`scripts/check-node-simple-web-engine2d-bitmap-evidence.shs`) is the valid
current web-renderer comparison lane. The older generic
`scripts/check-node-web-render-bitmap-evidence.shs` lane is stale until its
Simple fixture segfault is fixed and rerun.

### Pure Simple Web Rendering

Pure Simple Web Engine2D evidence, including
`doc/09_report/simple_web_engine2d_js_bitmap_evidence_2026-06-02.md` and
`doc/09_report/layered_simple_gui_web_engine2d_bitmap_evidence_2026-06-02.md`,
is renderer parity and regression evidence only. It proves Simple-owned
rendering can match web-compatible pixels, but WebRenderer/HTML layout remains
excluded from the pure GUI SMF/dynlib release path.

### GUI Rendering With Electron Or Tauri

Electron and Tauri are shell technologies. Electron provides Chromium/Node
browser-shell capture coverage through the Electron bitmap scripts. Tauri
provides optional adapter context through `tools/tauri-shell/` and
`doc/05_design/tauri_simple_integration_status_2026-03-23.md`, but its current
perf comparison is stale until `test/perf/tauri_equiv/tauri_reference/Cargo.toml`
is restored and the `args_get` workflow failure is fixed. Neither shell counts
as proof of the pure GUI SMF/dynlib release path.

### Resulting Priority Order

1. Pure Simple GUI library loaded from SMF/dynlib: release path.
2. CPU/software Engine2D: deterministic pixel reference.
3. Vulkan Engine2D: accelerated candidate after CPU parity and readback proof.
4. Pure Simple Web Engine2D plus Node/Bun/Electron: renderer parity only.
5. Tauri/Electron shells: optional adapter/capture lanes only.

## Implementation Phases

### Phase 1 - Pure GUI Library Boundary

- Define the public GUI library entry module under `src/lib/gui/`.
- Add records for `GuiInputEvent`, `GuiCommand`, `GuiCommandBatch`,
  `GuiDirtyRegion`, and `GuiPerfCounters` if equivalent records do not already
  exist.
- Ensure the module imports no WM, hosted, Simple Web, or native GUI runtime
  modules.
- Add unit coverage proving the public GUI module has deterministic command
  output for representative input sequences.

### Phase 2 - SMF/Dynlib Loader Path

- Add a macOS arm64 loader wrapper that opens the compiled GUI dynlib/SMF
  artifact through the pure SMF dynlib default, resolves the hot entry symbol
  once with SFFI dynload, and reuses it.
- Use the host `.so`/`.dylib` diagnostic lane only to prove callable symbol ABI
  and timing. Do not treat it as acceptance unless the loader is `smf_dynlib`.
- Implement wrapper, envelope, extraction, and probe orchestration in pure
  Simple. Do not introduce new Rust `rt_*` functions for SMF wrapping,
  extraction, or hot-call dispatch.
- If Simple cannot directly invoke the resolved native symbol, add a narrow C
  adapter that performs only the process-callable symbol call. Keep this C
  adapter outside the pure GUI library and outside pixel/rendering logic.
- Keep loader errors explicit: missing artifact, unsupported architecture,
  unresolved symbol, settlement failure, and fallback mode.
- Add a SimpleOS/QEMU loader adapter that uses the same artifact contract and
  maps command batches to the framebuffer/virtio presentation adapter.

### Phase 3 - Remove WM/Web Renderer Runtime Dependencies

- Move any release-lane imports of WM, `HostCompositor`, Simple Web renderer,
  HTML layout, or native GUI externs into smoke-only examples or adapter
  modules.
- Add a guard test or check script that fails if the pure GUI library release
  lane imports `rt_gui`, `rt_winit`, `SimpleWebRenderer`, or `WebRenderRequest`.
- Update evidence labels so hosted WM and web renderer reports cannot be read as
  acceptance evidence for this plan.

### Phase 4 - Hot Path Optimization

- Warm the loaded artifact before measurement.
- Preallocate and reuse event/command/dirty-region buffers.
- Avoid repeated symbol lookup, repeated SMF scans, string parsing, per-event
  heap churn, and runtime shell-outs in the measured path.
- Batch command transfer to the adapter.
- Do not edit raster pixel algorithms, glyph metrics, color math, layout pixel
  placement, or screenshot comparison logic in this phase.

### Phase 5 - Perf Probe And Evidence

- Add a perf probe for the macOS arm64 dynlib/SMF path with representative
  event batches: pointer move, click, key input, focus change, and invalidation.
- Emit machine-readable rows with p50/p95/p99/max microseconds and pass/fail
  against the 1000 us p99 target.
- Feed probe rows through `gui_dynlib_perf_report()` so interpreter/JIT/fallback
  measurements cannot satisfy the dynlib acceptance gate.
- Replace the probe's current `call_source=direct_simple` fallback with measured
  `call_source=dynlib_symbol_call` only after a pure Simple path or minimal C
  native-call adapter is implemented and verified.
- Record whether the probe used real dynlib, SMF loader, JIT, interpreter, or
  fallback. Fallback cannot satisfy the dynlib acceptance gate.
- Add an evidence report under `doc/09_report/` only after the probe has run.

### Phase 6 - Renderer And Shell Comparison Evidence

- Re-run the CPU/Vulkan parity evidence before any accelerated presentation
  backend is accepted for GUI command batches.
- Re-run Node.js and pure Simple web bitmap evidence when GUI command shapes,
  layout metadata, or Engine2D command emission changes.
- Re-run Electron live/generated bitmap evidence when browser-shell capture or
  web-renderer parity is used as regression context.
- Re-run Tauri comparison only as shell/adapter evidence. Do not treat Tauri
  or Electron success as proof that the pure GUI SMF/dynlib release path works.
- Record comparison reports under `doc/09_report/` with labels that state
  whether the evidence is release, acceleration, renderer parity, or shell-only.

### Phase 7 - QEMU ARM64 Parity

- Boot or smoke the SimpleOS ARM64 adapter with the same GUI artifact contract.
- Prove that the QEMU lane uses the pure GUI command ABI and not WM/web renderer
  runtime paths.
- Capture framebuffer evidence only as presentation proof; do not use pixel
  comparison to justify hot response performance.

## Verification Gates

- `SIMPLE_LIB=src bin/simple check src/lib/gui`
- `SIMPLE_LIB=src bin/simple test test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src bin/simple run src/app/gui_perf/smf_dynlib_probe.spl`
- `SIMPLE_LIB=src bin/simple test test/system/gui/linux_smf_dynlib_e2e_gate_system_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src SIMPLE_BIN=bin/simple bin/simple run src/app/gui_perf/macos_smf_dynlib_release_gate.spl`
- `SIMPLE_LIB=src bin/simple check src/os/smf`
- `SIMPLE_LIB=src bin/simple check src/os/posix`
- `SIMPLE_LIB=src bin/simple test test/unit/os/posix/dynlib_spec.spl --mode=interpreter`
- `SIMPLE_LIB=src bin/simple test test/unit/os/smf_runtime_spec.spl --mode=interpreter`
- Source guard: no new Rust runtime `rt_*` implementation files or Rust SFFI
  helpers are introduced for GUI SMF dynlib wrapping, extraction, or hot-call
  dispatch.
- Native fallback guard: if a native helper is unavoidable, it is C, isolated at
  the adapter boundary, and has tests proving pixel/rendering logic is unchanged.
- CPU/Vulkan comparison:
  `scripts/check-vulkan-engine2d-readback.shs` must pass with zero mismatches
  and no blur/tolerance evidence before Vulkan is accepted as an accelerated
  GUI presentation candidate.
- Node.js web rendering comparison:
  `scripts/check-node-simple-web-engine2d-bitmap-evidence.shs` must pass with
  exact ARGB/checksum parity before current Node Engine2D evidence is cited.
  `scripts/check-node-web-render-bitmap-evidence.shs` must also pass before the
  older generic Node web-render fixture is cited as fresh evidence.
- Pure Simple web rendering comparison:
  `scripts/check-simple-web-engine2d-js-bitmap-evidence.shs` must pass with
  exact parity and no blur/tolerance evidence before the pure Simple web lane is
  cited.
- Electron shell/rendering comparison:
  `scripts/check-electron-simple-web-engine2d-bitmap-evidence.shs` and
  `scripts/check-electron-live-bitmap-evidence.shs` must pass before Electron
  evidence is cited as browser-shell regression coverage.
- Tauri shell comparison:
  restore `test/perf/tauri_equiv/tauri_reference/Cargo.toml`, fix
  `workflow_driver.spl`/`simple_app.spl` argument access for the current CLI,
  then re-run `test/perf/tauri_equiv/README.md` workflows or the matching perf
  specs before Tauri evidence is cited as current shell/adapter evidence.
- Diagnostic only:
  `SIMPLE_LIB=src bin/simple compile src/app/gui_perf/pure_gui_hot_dynlib_export.spl --native --shared --strip -o build/gui/libpure_gui_hot.dylib`
  on macOS or `... -o build/gui/libpure_gui_hot.so` on Linux, followed by
  `SIMPLE_GUI_DYNLIB_ARTIFACT=<artifact> SIMPLE_LIB=src bin/simple run src/app/gui_perf/smf_dynlib_probe.spl`.
- Linux repeatable SMF dynlib evidence:
  `SIMPLE_LIB=src bin/simple run src/app/gui_perf/linux_smf_dynlib_e2e_gate.spl`
  must emit `GUI_LINUX_SMF_DYNLIB_E2E_GATE status=pass` on Linux after a
  `GUI_DYNLIB_PERF` row proving the SMF/SFFI hot-call path.
- Pure GUI release-lane dependency guard: no WM, Simple Web, or `rt_gui`/hosted
  runtime imports.
- macOS arm64 dynlib/SMF hot response probe: p99 < 1000 us after warmup.
- `GUI_DYNLIB_PERF` must report `loader=smf_dynlib`,
  `dynload=smf_dynlib`, `host_dynload=sffi`,
  `call_source=dynlib_symbol_call`, `pass=true`, and `error=`.
- The macOS release gate must emit `GUI_MAC_SMF_DYNLIB_RELEASE_GATE
  status=pass`, and the saved transcript must validate through
  `src/app/gui_perf/macos_smf_dynlib_transcript_check.spl`.
- QEMU ARM64 parity evidence: same GUI artifact contract reaches the adapter.
- `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Acceptance Gates

- The release path loads a pure Simple GUI SMF/dynlib artifact on macOS arm64.
- Hot response p99 is below 1 ms with real dynlib/SMF evidence.
- The measured path does not import WM, Simple Web renderer, browser renderer,
  or native GUI runtime externs.
- QEMU ARM64 uses the same GUI artifact contract for adapter presentation.
- Rendering pixel logic and pixel comparison thresholds are unchanged by the
  performance optimization.

## Documentation Updates Required

- Replace `gui_lib_mac_qemu_arm64_perf` option docs with final requirements
  after the user selects feature and NFR options.
- Update `doc/04_architecture/simple_gui_stack.md` to separate pure GUI library,
  SMF/dynlib loader, and adapter presentation layers.
- Update `doc/07_guide/ui_stack_guide.md` after the pure GUI library entrypoint
  and loader command are stable.
- Keep hosted WM and Simple Web reports labeled smoke/regression-only.
