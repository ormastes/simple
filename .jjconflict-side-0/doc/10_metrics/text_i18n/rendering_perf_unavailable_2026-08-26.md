# Multilingual rendering performance run — unavailable

The canonical performance spec
`test/05_perf/graphics_2d/shared_multilingual_gpu_fonts_perf_spec.spl` was
started to collect Engine2D Vulkan timing/resource high-water evidence and
isolated Engine2D/Engine3D legacy-versus-multiface RSS.

The run was stopped before admitting measurements because an unrelated
compiler process was simultaneously consuming approximately 18 GiB RSS at
100% CPU, with several other multi-GiB sessions active. That violates the
matched, controlled-host requirement and makes both latency and RSS results
inadmissible.

Status: `unavailable:host-resource-contention`.

No synthetic, fallback, partial, or contaminated value is treated as a PASS.
