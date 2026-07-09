# CPU-SIMD Render Scale Contract - 2026-07-08

Command:

```sh
sh scripts/check/check-cpu-simd-render-scale-contract.shs
```

Result:

```text
cpu_simd_render_scale_contract_status=pass
gui_perf_benchmark_backend=simple_web_cpu_simd
cpu_simd_render_scale_contract_mode=native
cpu_simd_render_scale_contract_dpi=300
cpu_simd_render_scale_contract_dpi_source=default
cpu_simd_render_scale_contract_sample_count=1
cpu_simd_render_scale_4k_pixels=3840x2160
cpu_simd_render_scale_4k_p50_frame_us=259857
cpu_simd_render_scale_4k_p95_frame_us=259857
cpu_simd_render_scale_4k_software_p50_frame_us=280087
cpu_simd_render_scale_4k_software_p95_frame_us=280087
cpu_simd_render_scale_4k_vs_software_p50_ratio_permille=1077
cpu_simd_render_scale_4k_checksum=sum32:32105444634193792
cpu_simd_render_scale_4k_software_checksum=sum32:32105444634193792
cpu_simd_render_scale_4k_software_checksum_parity=true
cpu_simd_render_scale_8k_pixels=7680x4320
cpu_simd_render_scale_8k_p50_frame_us=982085
cpu_simd_render_scale_8k_p95_frame_us=982085
cpu_simd_render_scale_8k_software_p50_frame_us=1050075
cpu_simd_render_scale_8k_software_p95_frame_us=1050075
cpu_simd_render_scale_8k_vs_software_p50_ratio_permille=1069
cpu_simd_render_scale_8k_checksum=sum32:135445232233405312
cpu_simd_render_scale_8k_software_checksum=sum32:135445232233405312
cpu_simd_render_scale_8k_software_checksum_parity=true
gui_perf_cpu_base_compare_status=measured
gui_perf_cpu_base_compare_source=cpu_simd_scale_contract
gui_perf_cpu_base_compare_pixels=7680x4320
gui_perf_cpu_base_compare_simple_backend=simple_web_cpu_simd
gui_perf_cpu_base_compare_simple_p50_ms=982.085
gui_perf_cpu_base_compare_baseline_backend=simple_web_software
gui_perf_cpu_base_compare_baseline_metric=p50_frame_ms
gui_perf_cpu_base_compare_baseline_ms=1050.075
gui_perf_cpu_base_compare_baseline_over_simple_ratio=1.069
gui_perf_cpu_base_compare_target_met=yes
```

The wrapper fails closed unless CPU-SIMD is selected, logical and physical
pixels match the requested full size, `screen_size_reduced=false`, 300dpi retina
metadata is present, checksum/nonzero-pixel proof exists, CPU-SIMD checksums
match the scalar software row for the same scene and dimensions, timing fields
are positive, software baseline timing is retained for comparison, and
fallback/unavailable fields are empty. Ratio fields are software p50 divided by
CPU-SIMD p50 in permille; values below `1000` mean the CPU-SIMD row is slower
than the scalar baseline for that size. Current retained evidence is faster at
both 4K and 8K on this host. The focused
`gui_perf_cpu_base_compare_*` fields use the same in-wrapper scalar software
baseline; external Cairo/GTK CPU drawing-library comparison remains in
`tools/gui_perf_bench/run_all_benchmarks.shs`.

The executable contract also covers DPI changeability with tiny dimensions:
`CPU_SIMD_RENDER_SCALE_DPI=220` must pass, report
`cpu_simd_render_scale_contract_dpi=220`, and mark
`cpu_simd_render_scale_contract_dpi_source=override`. The default path remains
300 DPI retina.

Additional focused coverage:

```sh
/home/ormastes/dev/pub/simple/bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl --mode=interpreter --clean
```

This verifies that explicit `gpu_paint=true` with `cpu_simd` routes layout fill
ops through Engine2D primitive dispatch and records SIMD fill hits, without
changing the default upload-bound GPU/CPU mirror path.
