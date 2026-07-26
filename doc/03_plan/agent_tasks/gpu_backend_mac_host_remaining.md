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

GPU_2D_LIVE_BACKEND=metal SIMPLE_BIN=bin/simple SIMPLE_LIB=src \
  sh scripts/check/check-macos-gpu-2d-live-evidence.shs
```

## Required evidence

- `build/metal_backend_mac_host/evidence.env` has
  `metal_generated_2d_readback_status=pass`.
- The generated lane records `module_verified=true`,
  `submit_attempted=true`, `readback_available=true`, and matching nonzero
  `fill`, `copy`, `alpha`, and `scroll` checksums.
- The framebuffer and CPU/Metal parity reports identify a real Metal device
  readback, not a CPU mirror or fallback.
- The live gate records the native device/queue/submit/readback receipt and
  matching pixels. Linux or unavailable output is not a pass.
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
