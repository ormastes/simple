# GUI Perf Measurement Agent Evidence - 2026-06-07

Scope: measurement/reporting only for the pure Simple GUI startup/render
slowness lane. No renderer implementation edits were made by this agent.

Parent revision measured:
`3d2cc6df8549cc9c57bbd4ad468540fb1e8b90a3`
(`perf(gui): preclassify simple selector matches`).

Host evidence:

- Host: `dl`
- OS: `x86_64 / Linux 6.8.0-117-generic`
- GPU: `NVIDIA RTX A6000`
- Benchmark artifact:
  `build/gui_perf_bench/measurement_agent_128x96_3_2026-06-07.md`

## 128x96 Text Fixture Profile

Command:

```sh
REPORT_PATH=build/gui_perf_bench/measurement_agent_128x96_3_2026-06-07.md \
BUILD_DIR=build/gui_perf_bench/measurement_agent_128x96_3 \
SKIP_PROFILE_REPORT_CONTRACT=1 \
tools/gui_perf_bench/run_all_benchmarks.shs --width 128 --height 96 --frames 3
```

Result:

| Lane | Status | p50 | p95 | Cold/startup evidence | Proof |
|------|--------|-----|-----|-----------------------|-------|
| `gtk3` | completed | `17.128ms` | `17.128ms` | `cold_startup_ms=105.34` | `pixel_count=12288` |
| `javascript_node_canvas` | completed | `0.105ms` | `0.164ms` | `cold_startup_ms=0.42` | `pixel_checksum=5953536` |
| `pure_simple_cuda` | completed | `527us` | `527us` | `artifact_load_us=140676`, `artifact_build_us=890` | `sum32:52571201863680`, `nonzero_pixels:12288` |
| `simple_web_software` | completed | `126466us` | `133121us` | `cold_start_us=126466` | `sum32:52601568094128`, `nonzero_pixels:12288` |

Skipped/unavailable lanes:

- `python_tkinter`: `python3 tkinter not available`
- `electron`: `electron binary not found`
- `tauri`: `tauri benchmark app not yet built; requires cargo-tauri + webview2`

Interpretation:

- The generated CUDA fill lane remains fast once the artifact is loaded:
  `p95_frame_us=527` for the same 128x96 pixel count.
- The Simple Web software text row still spends `133121us` p95 in
  `runtime_execution_path="engine2d-cpu_scalar"` and
  `operation_family="text_blit"`.
- This validates that recent selector/style fast paths and text-cache work did
  not break the measured software row, but the remaining frame cost is still
  CPU scalar text/layout execution rather than generated glyph-kernel work.
- The current `tools/gui_perf_bench/run_all_benchmarks.shs` in this checkout
  records `pure_simple_cuda` and `simple_web_software`; it does not yet emit the
  `simple_web_auto` static-cache row described by earlier reports. That row
  needs a separate harness refresh or a different canonical wrapper.

## Focused Spec Evidence

Commands that passed:

```sh
/home/ormastes/dev/pub/simple/bin/simple check \
  src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl \
  test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl
```

Result: passed, 2 files checked.

```sh
/home/ormastes/dev/pub/simple/bin/simple test \
  test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl \
  --mode=interpreter --no-cache
```

Result: passed, 57 scenarios.

```sh
/home/ormastes/dev/pub/simple/bin/simple test \
  test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl \
  --mode=interpreter --no-cache
```

Result: passed, 8 scenarios.

```sh
/home/ormastes/dev/pub/simple/bin/simple test \
  test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl \
  --mode=interpreter --no-cache
```

Result: passed, 2 scenarios.

```sh
/home/ormastes/dev/pub/simple/bin/simple test \
  test/01_unit/lib/common/text_layout/font_renderer_spec.spl \
  --mode=interpreter --no-cache
```

Result: passed, 19 scenarios.

```sh
/home/ormastes/dev/pub/simple/bin/simple test \
  test/05_perf/graphics_2d/backend_probe_spec.spl \
  --mode=interpreter --no-cache
```

Result: passed, 17 scenarios.

## Stale Path Evidence

These commands failed because the old paths do not exist in this checkout:

```sh
/home/ormastes/dev/pub/simple/bin/simple test \
  test/01_unit/lib/gc_async_mut/gpu/engine2d/font_renderer_spec.spl \
  --mode=interpreter --no-cache
```

```sh
/home/ormastes/dev/pub/simple/bin/simple test \
  test/01_unit/lib/gc_async_mut/gpu/engine2d/helpers_text_spec.spl \
  --mode=interpreter --no-cache
```

Current paths are:

- `test/01_unit/lib/common/text_layout/font_renderer_spec.spl`
- `test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl`

## Remaining Blockers

- Live GUI text still reports CPU scalar text blit in the measured software row;
  production Metal/CUDA/HIP/Vulkan/OpenCL glyph kernels still need to populate
  the vector/bitmap returned-glyph contract during real GUI execution.
- The benchmark wrapper in this checkout does not emit the earlier
  `simple_web_auto` static-cache row, so current measurement cannot revalidate
  that auto/backend-cache claim through `run_all_benchmarks.shs`.
- A dirty implementation file was present during this measurement:
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`.
  This report intentionally leaves that non-measurement change untouched.
