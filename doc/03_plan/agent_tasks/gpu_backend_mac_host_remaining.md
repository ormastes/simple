# macOS Metal Backend Host Work Remaining

## Scope

This lane is postponed from the current Linux host. It records the work needed
to obtain fresh Darwin evidence; it does not claim that Metal has run here.
The companion system spec is
`test/03_system/gpu/metal_backend_mac_host_spec.spl`.

## Exact macOS commands

Run from the repository root on a prepared macOS host:

```sh
xcrun --find metal
xcrun --find metallib
system_profiler SPDisplaysDataType

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  sh scripts/check/check-portable-compute-toolchains.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  BUILD_DIR=build/metal_backend_mac_host \
  REPORT_PATH=build/metal_backend_mac_host/report.md \
  sh scripts/check/check-metal-generated-2d-readback.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs

SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs

SIMPLE_LIB=src bin/simple test \
  test/03_system/gpu/metal_backend_mac_host_spec.spl \
  --mode=interpreter

GPU_2D_LIVE_BACKEND=metal SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  sh scripts/check/check-macos-gpu-2d-live-evidence.shs

SIMPLE_LIB=src bin/simple test \
  test/03_system/app/simpleos_gpu_host/macos_metal_processing_ir_failure_injection_spec.spl \
  --mode=interpreter

SIMPLE_LIB=src bin/simple test \
  test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl \
  --mode=interpreter
```

## Required evidence

- `build/metal_backend_mac_host/evidence.env` has
  `metal_generated_2d_readback_status=pass`.
- The generated lane records `module_verified=true`,
  `submit_attempted=true`, `readback_available=true`, and matching nonzero
  `fill`, `copy`, `alpha`, and `scroll` checksums.
- The framebuffer and CPU/Metal parity reports identify a real Metal device
  readback, not a CPU mirror or fallback.
- The production `MetalBackend` host scenario enables `gpu_only`, renders the
  16x16 clear/rectangle fixture, and proves exact pixels plus stable positive
  framebuffer handle and device identity across both device readbacks.
- The live gate records the native device/queue/submit/readback receipt and
  matching pixels. Linux or unavailable output is not a pass.
- The Vulkan ProcessingIR receipt records 64 exact values, fixed checksum
  `1082179840`, positive handle and identity, zero mismatches, device readback,
  and `cpu_fallback=false`.
- The Metal failure spec completes each bounded fault child without a timeout
  marker and preserves typed unavailable/init/submit/readback/mismatch reasons.
- Add canonical device identity plus exact expected-pixel, mismatch-count, and
  max-channel-delta fields before promoting the Vulkan lane from device-capture
  evidence to exact CPU/Vulkan parity.

## Ownership and postponement

- Merge owner: **Codex**.
- Final reviewer: **highest-capability/high model**, read-only after receipts
  exist.
- Postponed because this workspace is Linux and cannot produce Darwin Metal
  device evidence. The current task also forbids bootstrap/full builds; resume
  on a prepared macOS host with an accepted self-hosted `bin/simple` artifact.
- Do not close the GPU backend goal or convert this lane to PASS from source
  markers, cached artifacts, or a non-macOS unavailable result.
