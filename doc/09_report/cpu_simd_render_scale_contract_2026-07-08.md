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
cpu_simd_render_scale_4k_p50_frame_us=462364
cpu_simd_render_scale_4k_checksum=sum32:32105444634193792
cpu_simd_render_scale_8k_pixels=7680x4320
cpu_simd_render_scale_8k_p50_frame_us=1007526
cpu_simd_render_scale_8k_checksum=sum32:135445232233405312
```

The wrapper fails closed unless CPU-SIMD is selected, logical and physical
pixels match the requested full size, `screen_size_reduced=false`, 300dpi retina
metadata is present, checksum/nonzero-pixel proof exists, timing fields are
positive, and fallback/unavailable fields are empty.
