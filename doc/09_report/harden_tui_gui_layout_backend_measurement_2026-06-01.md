# Harden TUI/GUI Layout Backend Measurement Evidence

Date: 2026-06-01

## Command

```sh
for i in 1 2 3; do
  /usr/bin/time -f "sample=$i elapsed_s=%e max_rss_kb=%M" -a -o /tmp/wm_backend_measurement_time.txt \
    env SIMPLE_LIB=src src/compiler_rust/target/debug/simple \
    test test/system/wm_compare/backend_measurement_report_spec.spl --mode=interpreter --clean
done
stat -c 'simple_binary_size_bytes=%s' src/compiler_rust/target/debug/simple
```

## Raw Samples

```text
sample=1 elapsed_s=37.71 max_rss_kb=929240
sample=2 elapsed_s=38.58 max_rss_kb=930308
sample=3 elapsed_s=38.89 max_rss_kb=930160
simple_binary_size_bytes=454623792
```

## Parsed Evidence

```sdn
(backend_measurement
  requested: "cpu_simd"
  selected: "cpu_simd"
  status: "Initialized"
  command: "simple test test/system/wm_compare/backend_measurement_report_spec.spl"
  host: "linux-x86_64"
  warmup_count: 0
  sample_count: 3
  p50_us: 38580000
  p95_us: 38890000
  max_rss_kb: 930308
  binary_size_bytes: 454623792
  baseline_binary_size_bytes: 454623792
  binary_size_delta_bytes: 0
  render_readback_scope: "backend-measurement-spec-startup"
  scalar_baseline_compared: true
  fallback_used: false
  reason: "host measurement")
```

## Backend Lane Status

```sdn
(backend_measurement_matrix
  metal_status: "Unavailable"
  vulkan_status: "Unavailable"
  cuda_status: "Unavailable"
  cpu_simd_status: "Initialized"
  valid: true
  (backend_measurement requested: "metal" selected: "metal" status: "Unavailable" reason: "Metal requires macOS")
  (backend_measurement requested: "vulkan" selected: "vulkan" status: "Unavailable" reason: "vulkan probe unavailable in interpreter")
  (backend_measurement requested: "cuda" selected: "cuda" status: "Unavailable" reason: "CUDA runtime unavailable")
  (backend_measurement requested: "cpu_simd" selected: "cpu_simd" status: "Initialized" p50_us: 38580000 p95_us: 38890000 max_rss_kb: 930308 binary_size_bytes: 454623792 baseline_binary_size_bytes: 454623792 binary_size_delta_bytes: 0 scalar_baseline_compared: true fallback_used: false)
)
```

- CPU SIMD: initialized host measurement recorded above.
- Metal: unavailable on this Linux host.
- Vulkan: unavailable in the interpreter probe on this host.
- CUDA: unavailable on this host unless the local CUDA runtime/device probe initializes.

This is a representative host measurement for the backend measurement evidence path. It does not claim Metal, Vulkan, or CUDA acceleration on this host.
