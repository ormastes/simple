<!-- codex-research -->
# GPU Dynamic Backend and Full Offload — Domain Research

## Stable native plugin ABI

A narrow C ABI is the portable boundary for dynamically loaded providers.
POSIX exposes `dlopen`/`dlsym`; Windows exposes `LoadLibrary`/`GetProcAddress`.
Opaque handles and a versioned function table avoid exposing language-specific
object layouts across the ABI.

- POSIX: https://pubs.opengroup.org/onlinepubs/9699919799/functions/dlopen.html
- POSIX symbol lookup: https://pubs.opengroup.org/onlinepubs/009604299/functions/dlsym.html
- Windows lookup: https://learn.microsoft.com/windows/win32/api/libloaderapi/nf-libloaderapi-getprocaddress

Vulkan already uses explicit loader/driver interface negotiation, so a Simple
provider should use the official loader surface rather than vendor-private entry
points. CUDA similarly provides version-aware driver entry lookup through
`cuGetProcAddress`; mixing API versions is unsafe. Metal is an Apple framework
object protocol, so the portable Simple boundary should remain C-based while a
macOS provider owns Metal objects internally.

- Vulkan loader/driver interface: https://github.com/KhronosGroup/Vulkan-Loader/blob/main/docs/LoaderDriverInterface.md
- CUDA driver entry points: https://docs.nvidia.com/cuda/cuda-programming-guide/04-special-topics/driver-entry-point-access.html
- Metal devices: https://developer.apple.com/documentation/metal/mtldevice

## Completion and profiling

GPU dispatch is asynchronous. A portable receipt needs a completion token/event
rather than a global device wait: Vulkan has queue fences/semaphores, CUDA has
streams/events, and Metal has command-buffer completion handlers. Readback rules
remain backend-specific, including Metal managed-resource synchronization and
CUDA transfer synchronization behavior.

- Vulkan submit: https://registry.khronos.org/VulkanSC/specs/1.0-extensions/man/html/vkQueueSubmit.html
- CUDA asynchronous execution: https://docs.nvidia.com/cuda/cuda-programming-guide/02-basics/asynchronous-execution.html
- Metal completion: https://developer.apple.com/documentation/metal/mtlcommandbuffer/addcompletedhandler%28_%3A%29
- CUDA synchronization behavior: https://docs.nvidia.com/cuda/cuda-runtime-api/api-sync-behavior.html

Profiles must distinguish host API/marshalling time, queue wait, and device
execution. Small dispatches are frequently launch-bound; recorded/compiled graph
execution can amortize repeated work, but CPU logic is not part of a CUDA graph.
Profiling tools can perturb execution, so production timers and diagnostic-tool
profiles must be labeled separately.

- CUDA Graphs: https://docs.nvidia.com/cuda/cuda-programming-guide/04-special-topics/cuda-graphs.html
- Nsight Compute overhead: https://docs.nvidia.com/nsight-compute/ProfilingGuide/index.html

## Coarse-grained web/database data

Arrow's C Data Interface is prior art for a small stable in-process columnar ABI
with release callbacks. The C Device Interface adds device identity and optional
synchronization events for CUDA, Vulkan, and Metal. It is a useful model for
Simple batch descriptors, but raw-pointer structures are trusted in-process data;
untrusted providers require process isolation plus validated IPC.

- Arrow C Data Interface: https://arrow.apache.org/docs/format/CDataInterface.html
- Arrow C Device Interface: https://arrow.apache.org/docs/format/CDeviceDataInterface.html
- Arrow security: https://arrow.apache.org/docs/format/Security.html
- ADBC: https://arrow.apache.org/docs/format/ADBC.html

The resulting boundary should submit record batches/columns for fused filters,
projections, joins, aggregations, vector search, or transforms—not row-wise or
per-request GPU calls. WebGPU remains a separate browser-safe asynchronous path;
it is not a substitute for native Vulkan/CUDA/Metal provider evidence.

## Option-driving conclusions

- A versioned C function table with opaque sessions and completion tokens gives
  the strongest portable and testable interface.
- Per-symbol provider ABIs are simpler to extend incrementally but make atomic
  compatibility negotiation and lifetime ownership harder.
- Process isolation is appropriate for untrusted providers but adds IPC and copy
  costs; it should not be imposed on trusted first-party hot paths without a
  security requirement.
- Coarse batch descriptors align web/DB offload with launch and transfer costs.

