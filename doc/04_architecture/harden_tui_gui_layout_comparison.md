# Harden TUI/GUI Layout Comparison Architecture

Status: selected scope. User approved Feature Option 3 and NFR Option C on 2026-06-01.

## Scope Boundary

This feature hardens comparison correctness first, then makes size/performance claims backend-qualified. The current reachable implementation surface is:

- `src/os/compositor/screenshot_compare.spl` for compositor pixel comparison and diff images.
- `src/app/wm_compare/html_compat_part1.spl` and `html_compat_part3.spl` for Chrome/Simple fixture comparison.
- `src/app/wm_compare/site_corpus_compat.spl` for offline famous-site corpus pair comparison and production reports.
- `src/app/wm_compare/emulated_capture.spl` for deterministic shape capture.
- `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl` for backend availability and evidence summaries.

## Comparison Layers

Layer 1: capture validity. A capture is comparable only when it reports success, viewport metadata equals the requested viewport, and pixel count equals `width * height`.

Layer 2: exact pixels. Exact comparison is byte-for-byte equality across the full viewport. Invalid dimensions, truncated buffers, and metadata drift are failures, not zero-sized matches.

Layer 3: diagnostic tolerance. Perceptual or threshold metrics may explain drift but must not override exact acceptance unless a selected requirement explicitly changes the acceptance policy.

Layer 4: structural layout. TUI cell geometry and GUI/browser layout lines become a first-class structural report before pixel comparison. This layer builds on existing corpus layout-line reports and must add a shared report shape for TUI cell grids, GUI layout boxes, text line metrics, and geometry mismatches.

Layer 5: backend evidence. Metal, Vulkan, CUDA, and CPU SIMD lanes must report initialized, unavailable, or failed states explicitly. Software/scalar fallback is allowed for diagnostics, but must not be presented as accelerated backend proof.

## Failure Model

Comparison results must distinguish:

- `capture_failed`: source capture did not complete.
- `metadata_mismatch`: capture dimensions disagree with requested viewport.
- `pixel_size_mismatch`: pixel buffer length disagrees with viewport area.
- `exact_mismatch`: valid captures differ at one or more pixels.
- `diagnostic_tolerance_match`: perceptual/threshold metric is positive but not accepted under exact-only policy.
- `backend_unavailable`: backend/runtime/hardware is absent.
- `backend_failed`: backend runtime was present but initialization or context setup failed.

This prevents empty buffers, truncated captures, and unavailable hardware from looking like successful comparison evidence.

## Backend Evidence Contract

`BackendProbeResult` is the architecture boundary for acceleration claims. A backend lane is evidence-bearing only when:

- `requested_name` identifies the lane under test.
- `selected_name` is the same lane or an explicitly documented fallback.
- `status` is `Initialized`, `Unavailable`, `Failed`, or `Fallback`.
- `api_name`, `feature_gate`, and `shader_format` identify the runtime contract.
- capability flags distinguish compute, graphics, and present support.

The runtime summary must include Metal, Vulkan, CUDA, and CPU SIMD architecture status fields so reports cannot silently skip a requested backend.

## Performance And Size Evidence

The selected NFR requires the next architecture increment to add:

- warm startup timing for focused comparison specs and CLI comparison runs,
- max RSS capture for representative fixtures,
- binary size delta checks for changed comparison/backend CLI targets,
- p50/p95 render plus readback timings for each initialized backend,
- explicit unavailable reports for absent Metal, Vulkan, CUDA, or CPU SIMD lanes.

## Selected Scope Completion Items

- Implement or wire the shared structural layout report type.
- Add executable coverage for structural mismatch reporting.
- Add measurement evidence records for warm startup, max RSS, binary size deltas, and backend timing.
- Record initialized/unavailable/failed state for Metal, Vulkan, CUDA, and CPU SIMD lanes in final verify output.
