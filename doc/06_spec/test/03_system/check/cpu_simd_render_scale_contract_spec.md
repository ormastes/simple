# CPU SIMD Render Scale Contract

> The scale wrapper is the focused evidence gate for CPU-SIMD rendering at 4K and 8K. This spec keeps the wrapper honest without running full 8K inside the test: the source check guards the report fields, and the executable check overrides dimensions to a tiny fixture while preserving the same code path.

<!-- sdn-diagram:id=cpu_simd_render_scale_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cpu_simd_render_scale_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cpu_simd_render_scale_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cpu_simd_render_scale_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU SIMD Render Scale Contract

The scale wrapper is the focused evidence gate for CPU-SIMD rendering at 4K and 8K. This spec keeps the wrapper honest without running full 8K inside the test: the source check guards the report fields, and the executable check overrides dimensions to a tiny fixture while preserving the same code path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/07_guide/platform/gui_perf_benchmark_comparison.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/cpu_simd_render_scale_contract_spec.spl` |
| Updated | 2026-07-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The scale wrapper is the focused evidence gate for CPU-SIMD rendering at 4K and
8K. This spec keeps the wrapper honest without running full 8K inside the test:
the source check guards the report fields, and the executable check overrides
dimensions to a tiny fixture while preserving the same code path.

## Requirements

**Requirements:** N/A

- REQ-CPU-SIMD-SCALE-001: The scale wrapper emits CPU-SIMD and software p50/p95
  frame timing fields for the 4K and 8K rows.
- REQ-CPU-SIMD-SCALE-002: The scale wrapper emits a neutral p50 ratio field so
  reports can compare CPU-SIMD against the scalar software baseline without
  inventing a pass threshold.
- REQ-CPU-SIMD-SCALE-003: The wrapper emits `gui_perf_cpu_base_compare_*`
  fields for the focused CPU-SIMD vs scalar software baseline row.
- REQ-CPU-SIMD-SCALE-004: The wrapper remains runnable at small overridden
  dimensions for fast contract verification.
- REQ-CPU-SIMD-SCALE-005: The executable contract records native mode,
  default 300dpi retina density, and sample count so reports cannot pass with
  interpreter fallback or DPI drift.
- REQ-CPU-SIMD-SCALE-006: The wrapper records the CPU-SIMD/scalar run order so
  benchmark scheduling is explicit and can be reversed for follow-up evidence.

## Plan

**Plan:** doc/07_guide/platform/gui_perf_benchmark_comparison.md

1. Inspect the scale wrapper for retained timing and ratio fields.
2. Run the wrapper with tiny overridden dimensions.
3. Confirm the no-reduction, checksum parity, and comparison fields are present.
4. Guard the framebuffer allocation path until a safe typed owner fill bridge
   exists for browser layout buffers.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper uses the same `backend_measurement_software_export.spl` path for
CPU-SIMD and scalar software rows, then compares checksum and timing metadata.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/cpu_simd_render_scale_contract_spec.spl --mode=interpreter --clean
```

## Scenarios

### CPU SIMD render scale contract

#### exports software baseline timing comparison fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-cpu-simd-render-scale-contract.shs")
expect(script).to_contain("cpu_simd_render_scale_4k_p95_frame_us")
expect(script).to_contain("cpu_simd_render_scale_4k_software_p50_frame_us")
expect(script).to_contain("cpu_simd_render_scale_4k_software_p95_frame_us")
expect(script).to_contain("cpu_simd_render_scale_4k_vs_software_p50_ratio_permille")
expect(script).to_contain("cpu_simd_render_scale_8k_p95_frame_us")
expect(script).to_contain("cpu_simd_render_scale_8k_software_p50_frame_us")
expect(script).to_contain("cpu_simd_render_scale_8k_software_p95_frame_us")
expect(script).to_contain("cpu_simd_render_scale_8k_vs_software_p50_ratio_permille")
expect(script).to_contain("gui_perf_cpu_base_compare_status=measured")
expect(script).to_contain("gui_perf_cpu_base_compare_baseline_backend=simple_web_software")
expect(script).to_contain("gui_perf_benchmark_screen_size_reduced")
expect(script).to_contain("software_checksum_parity=true")
expect(script).to_contain("falling back to interpreter")
expect(script).to_contain("cpu_simd_render_scale_contract_mode=$EXEC_MODE")
expect(script).to_contain("cpu_simd_render_scale_contract_dpi=$DPI")
expect(script).to_contain("cpu_simd_render_scale_contract_sample_count=$SAMPLE_COUNT")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_RUN_ORDER")
expect(script).to_contain("cpu_simd_render_scale_contract_run_order=$RUN_ORDER")
expect(script).to_contain("gui_perf_cpu_base_compare_schedule_order=$RUN_ORDER")
expect(script).to_contain("unsupported_run_order_$RUN_ORDER")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_4K_WIDTH:-3840")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_8K_WIDTH:-7680")
expect(script).to_contain("run_export 4k_software \"$WIDTH_4K\" \"$HEIGHT_4K\" software 4k")
expect(script).to_contain("run_export 8k_software \"$WIDTH_8K\" \"$HEIGHT_8K\" software 8k")
expect(script).to_contain("_software_checksum_parity")
expect(script).to_contain("cpu_simd_render_scale_4k_software_checksum_parity=true")
expect(script).to_contain("cpu_simd_render_scale_8k_software_checksum_parity=true")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_4K_EXPECTED_CHECKSUM")
expect(script).to_contain("sum32:32105444634193792")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_8K_EXPECTED_CHECKSUM")
expect(script).to_contain("sum32:135445232233405312")
```

</details>

#### external cpu drawing baseline comparison records benchmark scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.

```simple
val script = file_read("tools/gui_perf_bench/run_all_benchmarks.shs")
expect(script).to_contain("gui_perf_cpu_base_compare_source=gui_perf_bench_external_cpu_library")
expect(script).to_contain("gui_perf_cpu_base_compare_pixels=$")
expect(script).to_contain("}x$")
expect(script).to_contain("gui_perf_cpu_base_compare_dpi=$DPI")
expect(script).to_contain("gui_perf_cpu_base_compare_frames=$FRAMES")
expect(script).to_contain("gui_perf_cpu_base_compare_simple_mode=$SIMPLE_WEB_CPU_MODE")
```

</details>

#### cpu simd text fixture skips the generic renderer wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.

```simple
val exporter = file_read("src/app/wm_compare/backend_measurement_software_export.spl")
expect(exporter).to_contain("fn _obvious_text_page")
expect(exporter).to_contain("backend == \"cpu_simd\" and _obvious_text_page(html)")
expect(exporter).to_contain("simple_web_layout_render_html_software_pixels(html, width, height)")
```

</details>

#### native array repeat fills the framebuffer without per-element push

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.

```simple
val source = file_read("src/runtime/runtime_native.c")
val repeat_start = source.find("SplArray* rt_array_repeat")
val repeat_body = source.slice(repeat_start, repeat_start + 700)
expect(repeat_body).to_contain("array->len = n")
expect(repeat_body).to_contain("data[i] = value")
expect(repeat_body.contains("rt_array_push")).to_equal(false)
val rust_source = file_read("src/compiler_rust/runtime/src/value/collections.rs")
val rust_repeat_start = rust_source.find("pub extern \"C\" fn rt_array_repeat")
val rust_repeat_body = rust_source.slice(rust_repeat_start, rust_repeat_start + 500)
expect(rust_repeat_body).to_contain("as_mut_slice().fill(value)")
expect(rust_repeat_body.contains("rt_array_push")).to_equal(false)
```

</details>

#### browser layout framebuffers stay on compiler array-repeat until a safe typed owner bridge exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.

```simple
val source = file_read("src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl")
expect(source).to_contain("[base; width * height]")
expect(source.contains("rt_engine2d_simd_fill_u32")).to_equal(false)
expect(source.contains("engine2d_simd_fill_row_u32")).to_equal(false)
expect(source.contains("rt_u32_alloc_filled")).to_equal(false)
```

</details>

#### runs small dimensions and keeps comparison fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-cpu-simd-render-scale-contract"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple" +
    " CPU_SIMD_RENDER_SCALE_4K_WIDTH=16 CPU_SIMD_RENDER_SCALE_4K_HEIGHT=16" +
    " CPU_SIMD_RENDER_SCALE_8K_WIDTH=32 CPU_SIMD_RENDER_SCALE_8K_HEIGHT=32" +
    " CPU_SIMD_RENDER_SCALE_RUN_ORDER=software_first CPU_SIMD_RENDER_SCALE_SAMPLE_COUNT=1 OUT_DIR=" + root + "/out" +
    " sh scripts/check/check-cpu-simd-render-scale-contract.shs > " + root + "/stdout.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val out = file_read(root + "/stdout.txt")
expect(out).to_contain("cpu_simd_render_scale_contract_status=pass")
expect(out).to_contain("cpu_simd_render_scale_contract_mode=native")
expect(out).to_contain("cpu_simd_render_scale_contract_dpi=300")
expect(out).to_contain("cpu_simd_render_scale_contract_dpi_source=default")
expect(out).to_contain("cpu_simd_render_scale_contract_sample_count=1")
expect(out).to_contain("cpu_simd_render_scale_contract_run_order=software_first")
expect(out).to_contain("cpu_simd_render_scale_4k_pixels=16x16")
expect(out).to_contain("cpu_simd_render_scale_8k_pixels=32x32")
expect(out).to_contain("cpu_simd_render_scale_4k_software_p50_frame_us=")
expect(out).to_contain("cpu_simd_render_scale_8k_software_p50_frame_us=")
expect(out).to_contain("cpu_simd_render_scale_4k_vs_software_p50_ratio_permille=")
expect(out).to_contain("cpu_simd_render_scale_8k_vs_software_p50_ratio_permille=")
expect(out).to_contain("gui_perf_cpu_base_compare_status=measured")
expect(out).to_contain("gui_perf_cpu_base_compare_pixels=32x32")
expect(out).to_contain("gui_perf_cpu_base_compare_simple_backend=simple_web_cpu_simd")
expect(out).to_contain("gui_perf_cpu_base_compare_baseline_backend=simple_web_software")
expect(out).to_contain("gui_perf_cpu_base_compare_schedule_order=software_first")
expect(out).to_contain("gui_perf_cpu_base_compare_target_met=")
expect(out).to_contain("cpu_simd_render_scale_4k_software_checksum_parity=true")
expect(out).to_contain("cpu_simd_render_scale_8k_software_checksum_parity=true")
```

</details>

#### runs small dimensions with an explicit dpi override

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.

```simple
val root = "build/test-cpu-simd-render-scale-contract-dpi-override"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple" +
    " CPU_SIMD_RENDER_SCALE_4K_WIDTH=8 CPU_SIMD_RENDER_SCALE_4K_HEIGHT=8" +
    " CPU_SIMD_RENDER_SCALE_8K_WIDTH=16 CPU_SIMD_RENDER_SCALE_8K_HEIGHT=16" +
    " CPU_SIMD_RENDER_SCALE_DPI=220 CPU_SIMD_RENDER_SCALE_SAMPLE_COUNT=1 OUT_DIR=" + root + "/out" +
    " sh scripts/check/check-cpu-simd-render-scale-contract.shs > " + root + "/stdout.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val out = file_read(root + "/stdout.txt")
expect(out).to_contain("cpu_simd_render_scale_contract_status=pass")
expect(out).to_contain("cpu_simd_render_scale_contract_dpi=220")
expect(out).to_contain("cpu_simd_render_scale_contract_dpi_source=override")
expect(out).to_contain("cpu_simd_render_scale_4k_pixels=8x8")
expect(out).to_contain("cpu_simd_render_scale_8k_pixels=16x16")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/07_guide/platform/gui_perf_benchmark_comparison.md](doc/07_guide/platform/gui_perf_benchmark_comparison.md)
- **Design:** [doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md](doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md](doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md)


</details>
