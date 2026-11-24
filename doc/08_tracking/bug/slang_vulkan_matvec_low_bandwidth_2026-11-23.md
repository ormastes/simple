# Vulkan matvec reaches only ~6 GB/s on the 32000x288 head shape

Measured 2026-11-23 on AMD Radeon 8065S (unified memory), seed release/1.0.0 0354c53a8be,
`test/03_system/lib/slang/feature/slang_pure_vulkan_matvec_perf_spec.spl`
(log: C:/dev/slang-logs/gpuall-vulkan/perf_run3.log):

- `gpu_excl_transfer_ms=5.901` per matvec of 32000x288 f32 (36.9 MB read) = ~6.3 GB/s; a second run on the same host while other sessions used the GPU gave 11.124 ms (perf_run4.log).
- Weight bulk upload once: 15 ms. Correctness: rel err 9.9e-8.

The device is far faster than this. Suspects, not yet profiled: one 256-lane workgroup per row
for only 288 columns (most lanes idle), and per-dispatch host cost in `vk_dispatch`
(descriptor update, command-buffer reset/record, submit, fence wait per op). Not fixed here.
