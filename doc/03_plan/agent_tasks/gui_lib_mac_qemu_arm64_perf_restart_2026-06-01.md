# GUI Lib macOS + QEMU ARM64 Perf Restart Plan - 2026-06-01

## Current Goal

Replan the macOS host GUI and SimpleOS QEMU ARM64 work around a real pure
Simple GUI path loaded from SMF/dynlib artifacts, with a measured sub-1 ms hot
response target. This restart explicitly removes WM and web-renderer runtime
extern dependencies from the production path and does not change rendering pixel
logic.

## Superseded Direction

Earlier notes treated hosted WM capture, `HostCompositor`, and
`simple_web_window_renderer.spl` as release evidence. That direction is now
smoke-only. It can remain useful for debugging presentation and screenshots, but
it is not the accepted implementation path for this goal.

The production lane is:

```text
macOS arm64 host
  -> SMF artifact for pure Simple GUI library
  -> native dynlib loader bridge
  -> pure Simple GUI event/update/render command API
  -> adapter presentation only

SimpleOS QEMU ARM64
  -> same SMF GUI artifact
  -> framebuffer/virtio adapter presentation only
```

## Non-Negotiable Constraints

- WM modules must not call `rt_gui_*`, `rt_winit_*`, `rt_sdl_*`, `rt_cocoa_*`,
  or web renderer runtime externs on the hot path.
- Web renderer modules are not part of the GUI library release lane. Do not
  route GUI app content through `SimpleWebRenderer`, HTML layout, browser
  surfaces, or `WebRenderRequest` to meet this goal.
- Runtime/native calls are allowed only at adapter boundaries: dynlib load,
  SMF mmap/settlement, platform event fetch, and final presentation.
- The sub-1 ms target is for event-to-updated-command response in the pure
  Simple GUI library after the SMF/dynlib artifact is loaded. Cold load,
  screenshot capture, QEMU boot, and pixel comparison are separate evidence.
- Rendering pixel logic is frozen for this optimization pass. Optimize loading,
  dispatch, caching, dirty-region bookkeeping, and bulk command transfer only.

## Current Evidence To Keep

- Existing hosted capture and WM/QEMU screenshot reports remain diagnostic
  evidence only.
- Existing Metal, CPU SIMD, framebuffer, and QEMU capture checks can verify
  presentation adapters, but they do not prove the pure Simple GUI library hot
  response target.
- Existing Simple Web and WM renderer tests remain regression coverage for their
  own features, not acceptance evidence for this goal.
- `src/lib/gui/pure_core.spl` now defines the pure Simple GUI value ABI for
  input events, command batches, dirty regions, and perf counters.
- `src/lib/gui/pure_smf_dynlib_perf.spl` now defines the SMF/dynlib acceptance
  report contract: real `smf_dynlib` mode, resolved hot symbol, no fallback, and
  p99 below 1000 us.
- `src/app/gui_perf/smf_dynlib_probe.spl` now emits the machine-readable
  `GUI_DYNLIB_PERF` row. It deliberately fails closed for direct Simple fallback
  samples until real dynlib symbol invocation is wired.
- `src/app/gui_perf/pure_gui_hot_dynlib_export.spl` now provides a pure Simple
  exported hot symbol for host `.so`/`.dylib` diagnostics. This lane has proven
  callable dynlib overhead, but it is still rejected as `not-smf-dynlib`.
- `src/compiler_rust/runtime/src/value/sffi/dyncall.rs` now implements the
  i64-only `rt_dyncall_*` runtime bridge used by `dynlib_call_1`.
- `doc/08_tracking/bug/gui_smf_dynlib_hot_call_runtime_missing_2026-06-01.md`
  now tracks the remaining artifact/evidence gap after the runtime bridge was
  added.

## Implementation Restart Tasks

1. Add or identify the pure Simple GUI library entry surface that can be emitted
   as SMF and loaded through a macOS arm64 dynlib bridge.
2. Define a small command ABI for GUI input events, state updates, dirty regions,
   and render command batches. Keep pixels opaque to this pass.
3. Move any WM/web-renderer calls out of the release path and into adapter or
   smoke-only wrappers.
4. Add a focused perf probe that warms the dynlib/SMF artifact, sends
   representative GUI events, and records p50/p95/p99 response in microseconds.
5. Gate success on p99 less than 1000 us for the hot response path on the named
   macOS arm64 host profile, with machine details recorded in the evidence.
6. Implement or replace `rt_dyncall_*` so the measured path can report
   `call_source=dynlib_symbol_call` instead of `direct_simple`.
7. Add QEMU ARM64 parity evidence that the same SMF GUI artifact can drive the
   SimpleOS adapter without importing WM or web renderer runtime paths.

## Resume Commands

```bash
rg -n "rt_gui|rt_winit|rt_sdl|rt_cocoa|SimpleWebRenderer|WebRenderRequest" src/os src/lib examples/simple_os -g '*.spl'
SIMPLE_LIB=src src/compiler_rust/target/debug/simple check src/os/smf src/os/posix src/lib/gui
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/gui/pure_smf_dynlib_perf_spec.spl --mode=interpreter --no-cache
mkdir -p build/gui
SIMPLE_LIB=src src/compiler_rust/target/debug/simple compile src/app/gui_perf/pure_gui_hot_dynlib_export.spl --native --shared --strip -o build/gui/libpure_gui_hot.so
SIMPLE_LIB=src SIMPLE_GUI_DYNLIB_ARTIFACT=build/gui/libpure_gui_hot.so src/compiler_rust/target/debug/simple run src/app/gui_perf/smf_dynlib_probe.spl
SIMPLE_LIB=src src/compiler_rust/target/debug/simple run src/app/gui_perf/smf_dynlib_probe.spl
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/os/posix/dynlib_spec.spl --mode=interpreter --no-cache
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/os/smf_runtime_spec.spl --mode=interpreter --no-cache
find doc/06_spec -name '*_spec.spl' | wc -l
```

## Open Evidence Gaps

- No current evidence proves a pure Simple GUI SMF/dynlib hot event response
  below 1 ms.
- The runtime can now call a resolved dynlib symbol, but no macOS arm64
  SMF/dynlib artifact is configured in current evidence, so the probe still
  reports `pass=false error=missing-artifact-path`.
- Current hosted and QEMU WM paths still contain direct runtime GUI externs and
  therefore cannot close this goal.
- Final requirements are still option files; the user selection step must be
  completed before release-grade verification.

## Sync Note

This restart plan supersedes hosted WM/web renderer release evidence. A future
commit should include the pure GUI dynlib perf probe and only then update the
evidence report.
