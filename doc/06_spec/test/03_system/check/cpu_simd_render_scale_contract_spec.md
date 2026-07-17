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
| 9 | 9 | 0 | 0 |

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
| Updated | 2026-07-16 |
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
- REQ-CPU-SIMD-SCALE-007: The wrapper reports whether the selected production
  binary links the Engine2D SIMD row externs and can require that in strict mode.
- REQ-CPU-SIMD-SCALE-008: The wrapper reports whether runtime sources changed
  after the selected production binary and can require freshness in strict mode.
- REQ-CPU-SIMD-SCALE-009: The wrapper can require the canonical Engine2D SIMD
  arch matrix and expose x86_64, AArch64, and RISC-V target-binary pass fields
  without rerunning render benchmarks.
- REQ-CPU-SIMD-SCALE-010: CPU-SIMD rows require positive provider/native hits,
  while scalar software rows require zero SIMD hits.

## Plan

**Plan:** doc/07_guide/platform/gui_perf_benchmark_comparison.md

1. Inspect the scale wrapper for retained timing and ratio fields.
2. Run the wrapper with tiny overridden dimensions.
3. Confirm the no-reduction, checksum parity, and comparison fields are present.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper uses the same `backend_measurement_software_export.spl` harness for
CPU-SIMD and scalar rows. The harness passes the configured backend through the
canonical Simple Web renderer before comparing checksum and timing metadata.

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

Runnable source: 54 lines folded for reproduction.
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
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_REQUIRE_ENGINE2D_BINARY")
expect(script).to_contain("binary_has_engine2d_simd_externs")
expect(script).to_contain("nm -P -g")
expect(script).to_contain("grep -q 'weak external'")
expect(script).to_contain("rt_engine2d_simd_fill_row_u32")
expect(script).to_contain("rt_engine2d_simd_fill_rows_u32")
expect(script).to_contain("rt_engine2d_simd_fill_span_u32")
expect(script).to_contain("rt_engine2d_simd_copy_row_u32")
expect(script).to_contain("rt_engine2d_simd_copy_span_u32")
expect(script).to_contain("rt_engine2d_simd_blend_row_u32")
expect(script).to_contain("cpu_simd_render_scale_engine2d_binary_link_status=$ENGINE2D_BINARY_LINK_STATUS")
expect(script).to_contain("engine2d_simd_externs_not_linked_in_simple_bin")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_REQUIRE_RUNTIME_FRESH")
expect(script).to_contain("runtime_source_fresh_status")
expect(script).to_contain("src/runtime/runtime_simd_dispatch.c")
expect(script).to_contain("runtime_sources_newer_than_simple_bin")
expect(script).to_contain("cpu_simd_render_scale_runtime_source_fresh_status=$RUNTIME_SOURCE_FRESH_STATUS")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_4K_WIDTH:-3840")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_8K_WIDTH:-7680")
expect(script).to_contain("run_export 4k_software \"$WIDTH_4K\" \"$HEIGHT_4K\" software 4k")
expect(script).to_contain("run_export 8k_software \"$WIDTH_8K\" \"$HEIGHT_8K\" software 8k")
expect(script).to_contain("_software_checksum_parity")
expect(script).to_contain("cpu_simd_render_scale_4k_software_checksum_parity=true")
expect(script).to_contain("cpu_simd_render_scale_8k_software_checksum_parity=true")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_4K_EXPECTED_CHECKSUM")
expect(script).to_contain("sum32:35624123900197965")
expect(script).to_contain("CPU_SIMD_RENDER_SCALE_8K_EXPECTED_CHECKSUM")
expect(script).to_contain("sum32:142496654044810320")
expect(script).to_contain("require_value \"${label}_native_simd_executed\" \"true\"")
expect(script).to_contain("require_positive \"${label}_simd_provider_hits\"")
expect(script).to_contain("require_positive \"${label}_native_simd_hits\"")
expect(script).to_contain("require_value \"${label}_software_simd_provider_hits\" \"0\"")
expect(script).to_contain("require_value \"${label}_software_native_simd_executed\" \"false\"")
expect(script).to_contain("/usr/bin/time -f 'max_rss_kb=%M'")
expect(script).to_contain("measured_rss")
expect(script).to_contain("[ \"$run_rc\" -eq 0 ] || return \"$run_rc\"")
```

</details>

#### external cpu drawing baseline comparison records benchmark scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("tools/gui_perf_bench/run_all_benchmarks.shs")
expect(script).to_contain("write_simple_web_export_entry")
expect(script).to_contain("software_only_render_loop_export_values")
expect(script).to_contain("SIMPLE_WEB_CPU_SIMD_ENTRY")
expect(script).to_contain("SIMPLE_WEB_SOFTWARE_ENTRY")
expect(script).to_contain("gui_perf_cpu_base_compare_source=gui_perf_bench_external_cpu_library")
expect(script).to_contain("gui_perf_cpu_base_compare_pixels=$")
expect(script).to_contain("}x$")
expect(script).to_contain("gui_perf_cpu_base_compare_dpi=$DPI")
expect(script).to_contain("gui_perf_cpu_base_compare_frames=$FRAMES")
expect(script).to_contain("gui_perf_cpu_base_compare_simple_mode=$SIMPLE_WEB_CPU_MODE")
expect(script).to_contain("gui_perf_cpu_base_compare_simple_launch_kind=run")
expect(script).to_contain("gui_perf_cpu_base_compare_simple_native_artifact_used=false")
expect(script).to_contain("gui_perf_cpu_base_compare_simd_provider_hits=")
expect(script).to_contain("gui_perf_cpu_base_compare_native_simd_executed=")
```

</details>

#### software exporter routes the configured backend through the canonical renderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exporter = file_read("src/app/wm_compare/backend_measurement_software_export.spl")
expect(exporter.contains("web_render_backend")).to_equal(false)
expect(exporter).to_contain("fn _render_software_pixels(html: text, width: i32, height: i32, backend: text) -> [u32]")
expect(exporter).to_contain("raw.parse_int() ?? fallback")
expect(exporter).to_contain("raw.parse_int() ?? fallback.to_i64()")
expect(exporter).to_contain("simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(html, width, height, backend)")
expect(exporter.contains("simple_web_render_html_to_pixels_with_engine2d_backend")).to_equal(false)
expect(exporter).to_contain("_render_software_pixels(html, width, height, backend)")
val renderer = file_read("src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_cpu.spl")
expect(renderer).to_contain("pub fn simple_web_render_html_to_pixels_with_cpu_draw_ir_backend(html: text, width: i32, height: i32, backend_name: text) -> [u32]:")
expect(renderer).to_contain("simple_web_layout_render_html_draw_ir_cpu_bitmap(html, width, height)")
expect(renderer).to_contain("CpuBackend.create_simd()")
expect(renderer).to_contain("CpuBackend.create()")
expect(renderer.contains("use std.gc_async_mut.gpu.engine2d.engine")).to_equal(false)
val semantic_renderer = file_read("src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl")
expect(semantic_renderer).to_contain("compute_styles(nodes, rules, child_index, false, vector_fonts)")
expect(semantic_renderer).to_contain("if vector_fonts and nd.tag == \"#text\"")
expect(semantic_renderer).to_contain("val canvas_color = _web_canvas_background(nodes, styles, argb(255, 255, 255))")
expect(semantic_renderer).to_contain("commands = [_html_draw_ir_canvas_command(width, height, canvas_color)] + commands")
expect(semantic_renderer).to_contain("if styles[i].visibility_hidden:")
expect(exporter).to_contain("simd_provider_hits:")
expect(exporter).to_contain("native_simd_hits:")
expect(exporter).to_contain("gui_perf_benchmark_simd_provider_hits=")
expect(exporter).to_contain("gui_perf_benchmark_native_simd_hits=")
expect(exporter).to_contain("gui_perf_benchmark_native_simd_executed=")
expect(exporter).to_contain("_native_simd_executed_text(native_simd_hits)")
val simd_provider = file_read("src/lib/nogc_sync_mut/gpu/engine2d/simd_provider.spl")
expect(simd_provider).to_contain("pub fn reset_simd_hits() -> ():")
expect(simd_provider).to_contain("_simd_vectorize_changes = 0\n    return ()")
val vulkan_session = file_read("src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl")
expect(vulkan_session).to_contain("me init_device() -> text:")
expect(vulkan_session).to_contain("me create_command_pool() -> text:")
expect(vulkan_session).to_contain("me create_pipeline_cache() -> text:")
expect(vulkan_session).to_contain("me load_shader(name: text) -> i64:")
expect(vulkan_session).to_contain("me release() -> text:")
val directx_backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl")
expect(directx_backend).to_contain("me _native_execute_once():")
val arabic = file_read("src/lib/skia/feature/shaper/selected_arabic.spl")
expect(arabic).to_contain("fn _arabic_coverage_index")
expect(arabic).to_contain("fn _arabic_single")
expect(arabic).to_contain("while index < working.len():")
val devanagari = file_read("src/lib/skia/feature/shaper/selected_devanagari.spl")
expect(devanagari).to_contain("fn _devanagari_coverage_index")
expect(devanagari).to_contain("fn _devanagari_single")
val layout = file_read("src/lib/skia/feature/glyph/ot_parser_layout.spl")
expect(layout).to_contain("fn _layout_coverage_index")
val font_renderer = file_read("src/lib/nogc_sync_mut/text_layout/font_renderer.spl")
expect(font_renderer).to_contain("val found = _resolved_font_metric_values[index]")
expect(font_renderer).to_contain("_resolved_font_metric_lock.unlock(0)\n            return found")
expect(font_renderer).to_contain("return found")
expect(font_renderer.contains("var found: ResolvedFontMetrics?")).to_equal(false)
val emu_adv = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_emu_adv.spl")
expect(emu_adv).to_contain("fn emu_draw_image_blend(mut core: RenderBackend")
expect(emu_adv).to_contain("emu_draw_image_blend(core, dst_x")
expect(emu_adv.contains("core.draw_image_blend(")).to_equal(false)
val emu = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl")
expect(emu.contains("fn emu_draw_image_blend(mut core: RenderBackend")).to_equal(false)
val vulkan_backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl")
expect(vulkan_backend).to_contain("me mark_completion_unknown():")
val engine = file_read("src/lib/gc_async_mut/gpu/engine2d/engine.spl")
expect(engine).to_contain("vulkan.mark_completion_unknown()")
expect(engine.contains("vulkan.completion_unknown = true")).to_equal(false)
expect(engine).to_contain("evidence.clear_fallback_pixels()")
expect(engine.contains("evidence.fallback_pixels = []")).to_equal(false)
expect(engine).to_contain("software_backend: SoftwareBackend? = nil")
expect(engine).to_contain("cpu_backend: CpuBackend? = nil")
expect(engine).to_contain("directx_backend: DirectXBackend? = nil")
expect(engine).to_contain("emu_draw_image_blend(self.backend, x, y, w, h, pixels)")
expect(engine.contains("self.backend.draw_image_blend(")).to_equal(false)
expect(engine).to_contain("val active_vulkan = self.vulkan_backend")
val vulkan_font_types = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_types.spl")
expect(vulkan_font_types).to_contain("me clear_fallback_pixels():")
```

</details>

#### typed software exporter reports true nearest rank percentiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exporter = file_read("src/app/wm_compare/backend_measurement_software_export.spl")
expect(exporter).to_contain("fn _percentile_nearest_rank")
expect(exporter).to_contain("((sorted.len() * pct + 99) / 100) - 1")
expect(exporter).to_contain("if rank >= sorted.len()")
val percentile_start = exporter.find("fn _percentile_nearest_rank")
val percentile_body = exporter.slice(percentile_start, percentile_start + 350)
expect(percentile_body.contains("sorted[sorted.len() - 1]")).to_equal(false)
```

</details>

#### native array repeat fills the framebuffer with memcpy doubling

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/runtime/runtime_native.c")
val repeat_start = source.find("SplArray* rt_array_repeat")
val repeat_body = source.slice(repeat_start, repeat_start + 700)
expect(source).to_contain("static SplArray* rt_core_array_new_fill(int64_t cap, uint8_t flags, int zero_items)")
expect(source).to_contain("zero_items ? calloc((size_t)actual_cap, elem_size) : malloc((size_t)actual_cap * elem_size)")
expect(repeat_body).to_contain("rt_core_array_new_fill(n, 0, 0)")
expect(repeat_body).to_contain("array->len = n")
expect(repeat_body).to_contain("data[0] = value")
expect(repeat_body).to_contain("memcpy(data + filled, data")
expect(repeat_body.contains("rt_array_push")).to_equal(false)
val core_source = file_read("src/runtime/simple_core/core_array_ops.spl")
val core_repeat_start = core_source.find("pub fn rt_array_repeat")
val core_repeat_body = core_source.slice(core_repeat_start, core_repeat_start + 500)
expect(core_source).to_contain("fn rt_array_repeat_new_uninit")
expect(core_source).to_contain("val items = malloc(actual_cap * 8)")
expect(core_repeat_body).to_contain("rt_array_repeat_new_uninit(count)")
expect(core_repeat_body).to_contain("spl_store_i64(items, 0, value)")
expect(core_repeat_body).to_contain("memcpy(items + filled * 8, items")
val rust_source = file_read("src/compiler_rust/runtime/src/value/collections.rs")
val rust_repeat_start = rust_source.find("pub extern \"C\" fn rt_array_repeat")
val rust_repeat_body = rust_source.slice(rust_repeat_start, rust_repeat_start + 500)
expect(rust_repeat_body).to_contain("as_mut_slice().fill(value)")
expect(rust_repeat_body.contains("rt_array_push")).to_equal(false)
```

</details>

#### browser layout framebuffers use the safe owner fill facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = file_read("src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl")
expect(source).to_contain("fn browser_layout_framebuffer_filled")
expect(source).to_contain("replace internals here if native fill grows a safer ABI")
expect(source).to_contain("[base; width * height]")
expect(source).to_contain("var fb = browser_layout_framebuffer_filled(base, width, height)")
expect(source.contains("rt_engine2d_simd_fill_u32")).to_equal(false)
expect(source.contains("engine2d_simd_fill_row_u32")).to_equal(false)
expect(source.contains("rt_u32_alloc_filled")).to_equal(false)
```

</details>

#### runs small dimensions and keeps comparison fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-cpu-simd-render-scale-contract"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && SIMPLE_BIN='" + _test_simple_bin() + "'" +
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
expect(out).to_contain("cpu_simd_render_scale_engine2d_binary_link_status=")
expect(out).to_contain("cpu_simd_render_scale_engine2d_binary_link_required=0")
expect(out).to_contain("cpu_simd_render_scale_runtime_source_fresh_status=")
expect(out).to_contain("cpu_simd_render_scale_runtime_source_fresh_required=0")
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
expect(out).to_contain("gui_perf_cpu_base_compare_simd_provider_hits=")
expect(out).to_contain("gui_perf_cpu_base_compare_native_simd_executed=")
expect(out).to_contain("cpu_simd_render_scale_4k_software_checksum_parity=true")
expect(out).to_contain("cpu_simd_render_scale_8k_software_checksum_parity=true")
```

</details>

#### runs small dimensions with an explicit dpi override

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-cpu-simd-render-scale-contract-dpi-override"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && SIMPLE_BIN='" + _test_simple_bin() + "'" +
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

<details>
<summary>Advanced: requires arch matrix target binaries without rerunning render benchmarks</summary>

#### requires arch matrix target binaries without rerunning render benchmarks

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-cpu-simd-render-scale-arch-matrix-only"
val env_path = root + "/evidence.env"
val command =
    "rm -rf " + root + " && mkdir -p " + root +
    " && printf '%s\\n' " +
    "'cpu_simd_engine2d_arch_matrix_status=pass' " +
    "'cpu_simd_engine2d_arch_matrix_x86_64_target_binary_status=pass' " +
    "'cpu_simd_engine2d_arch_matrix_aarch64_target_binary_status=pass' " +
    "'cpu_simd_engine2d_arch_matrix_riscv64_target_binary_status=pass' > " + env_path +
    " && CPU_SIMD_RENDER_SCALE_ARCH_MATRIX_ONLY=1" +
    " CPU_SIMD_RENDER_SCALE_REQUIRE_ARCH_MATRIX=1" +
    " CPU_SIMD_RENDER_SCALE_ARCH_MATRIX_ENV=" + env_path +
    " sh scripts/check/check-cpu-simd-render-scale-contract.shs > " + root + "/stdout.txt"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val out = file_read(root + "/stdout.txt")
expect(out).to_contain("cpu_simd_render_scale_contract_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_required=1")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_x86_64_target_binary_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_aarch64_target_binary_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_riscv64_target_binary_status=pass")
expect(out).to_contain("cpu_simd_render_scale_arch_matrix_only=1")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/07_guide/platform/gui_perf_benchmark_comparison.md](doc/07_guide/platform/gui_perf_benchmark_comparison.md)
- **Design:** [doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md](doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md](doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md)


</details>
