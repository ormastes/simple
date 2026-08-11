# Bug: candidate Vulkan sources report no real device enumeration data

**Date:** 2026-08-11
**Boundary:** `vulkan.device.enumeration@1` (lane L2 of the board Vulkan
counterpart effort)
**Files:**
- `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl:52-59` (`_venus_transport_send`)
- `src/os/drivers/gpu/gpu_vendor_probe.spl:143-153` (`QualcommArmGpuProbe.probe()`, and
  the identically-shaped `CudaGpuProbe`/`AmdGpuProbe`/`IntelGpuProbe`/`RiscvSoftGpuProbe`
  constructors)

## What was checked

Both candidate files were read in full to see whether Simple reports anything
real for physical-device enumeration (device name/vendor/device id/API
version, queue families, memory heaps/types, limits).

- `vulkan_icd_virtio.spl`: the module docstring (line 1-9) already says the
  transport is "modeled ... pending virtio-gpu kernel driver integration".
  `_venus_transport_send` (line 52-59) always returns
  `VenusCallResult(is_ok: true, error: "", handle: _venus_handle_ctr, payload_size: 0)`
  where `_venus_handle_ctr` is a local incrementing counter — a fabricated
  handle, not data read from any device. There is no function anywhere in the
  183-line file that reads or reports a device name, a queue family, or a
  memory heap/type.
- `gpu_vendor_probe.spl`: every one of the five vendor probes
  (`CudaGpuProbe`, `AmdGpuProbe`, `IntelGpuProbe`, `QualcommArmGpuProbe`,
  `RiscvSoftGpuProbe`) hard-codes `device_id: 0` in its `.probe()`
  constructor, and each class's own `is_available()` is defined as
  `self.device_id > 0` — so every probe self-reports unavailable by
  construction. The module docstring (line 5-7) confirms this is intentional:
  "Each probe returns an 'unavailable' descriptor by default; hardware-specific
  layers fill real values when the device is detected" — but no such
  hardware-specific layer exists yet.

## Verdict

Neither file reports anything real at the `vulkan.device.enumeration@1`
boundary today. This is a STUB, confirmed by reading, not assumed.

## Unblock condition

Either file starts reporting real enumeration data once (a) virtio-gpu ring
I/O is wired to `_venus_transport_send` and the Venus `VK_STRUCTURE_TYPE_*`
device/queue/memory query responses are decoded, or (b) a vendor probe is
backed by a real ICD/DRM query (e.g. reading `vkEnumeratePhysicalDevices`
output for a bound Vulkan loader) instead of a hard-coded `device_id: 0`. At
that point `candidate_enumeration_is_available()` in
`src/os/drivers/gpu/board_vulkan/boundary_enumeration_provider.spl` should
flip and a real `DeviceEnumerationRecord` should be produced from the
candidate's actual data instead of `ProviderStatus.unavailable`.

## Disposition for this lane (L2)

The `vulkan.device.enumeration@1` boundary, schema, comparison relation and
Mesa-lavapipe counterpart fixture were still built in full
(`src/os/drivers/gpu/board_vulkan/boundary_enumeration_model.spl`,
`boundary_enumeration_provider.spl`,
`test/01_unit/os/vulkan/device_enumeration_boundary_spec.spl`). The candidate
side honestly reports `ProviderStatus.unavailable` rather than a fabricated
passing record — the spec proves the framework correctly refuses to treat
`unavailable` as a pass, per `.claude/rules/board-runnable.md` and the
counterpart plan's "unavailable is never a pass" rule.
