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
cpu_simd_render_scale_4k_p50_frame_us=248633
cpu_simd_render_scale_4k_p95_frame_us=248633
cpu_simd_render_scale_4k_software_p50_frame_us=243930
cpu_simd_render_scale_4k_software_p95_frame_us=243930
cpu_simd_render_scale_4k_vs_software_p50_ratio_permille=981
cpu_simd_render_scale_4k_checksum=sum32:32105444634193792
cpu_simd_render_scale_4k_software_checksum=sum32:32105444634193792
cpu_simd_render_scale_4k_software_checksum_parity=true
cpu_simd_render_scale_8k_pixels=7680x4320
cpu_simd_render_scale_8k_p50_frame_us=1132428
cpu_simd_render_scale_8k_p95_frame_us=1132428
cpu_simd_render_scale_8k_software_p50_frame_us=945236
cpu_simd_render_scale_8k_software_p95_frame_us=945236
cpu_simd_render_scale_8k_vs_software_p50_ratio_permille=834
cpu_simd_render_scale_8k_checksum=sum32:135445232233405312
cpu_simd_render_scale_8k_software_checksum=sum32:135445232233405312
cpu_simd_render_scale_8k_software_checksum_parity=true
```

The wrapper fails closed unless CPU-SIMD is selected, logical and physical
pixels match the requested full size, `screen_size_reduced=false`, 300dpi retina
metadata is present, checksum/nonzero-pixel proof exists, CPU-SIMD checksums
match the scalar software row for the same scene and dimensions, timing fields
are positive, software baseline timing is retained for comparison, and
fallback/unavailable fields are empty. Ratio fields are software p50 divided by
CPU-SIMD p50 in permille; values below `1000` mean this host still needs CPU
SIMD render-loop optimization before a speedup claim.

Additional focused coverage:

```sh
/home/ormastes/dev/pub/simple/bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl --mode=interpreter --clean
```

This verifies that explicit `gpu_paint=true` with `cpu_simd` routes layout fill
ops through Engine2D primitive dispatch and records SIMD fill hits, without
changing the default upload-bound GPU/CPU mirror path.
