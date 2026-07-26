# Native Backend Probe Enum Comparison

## Status

Open. TODO 580 Vulkan evidence blocker.

## Evidence

A cached-Stage3, 184-module Engine2D archive links without generated stubs
against an isolated Vulkan/CUDA runtime provider. On the NVIDIA Vulkan ICD the
native probe reports `status=Initialized`, `compute=true`, and `graphics=true`.

The same returned `BackendProbeResult` evaluates both `probe.is_ok()` and
`probe.status == BackendStatus.Initialized` as false.
`backend_status_text(probe.status)` prints `Initialized`, proving the field is
present but the cross-module comparison ABI is wrong.

## Resume

Fix the cached/native enum return or comparison lowering, or rebuild the
source-matched CLI incrementally. Then run
`scripts/check/check-vulkan-engine2d-readback.shs` and require native present,
device readback, positive handle/device identity, and zero pixel mismatches.
