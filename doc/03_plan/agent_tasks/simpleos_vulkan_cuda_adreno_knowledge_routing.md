# Agent Tasks: SimpleOS GPU and Knowledge Routing

| Lane | Scope | Owner |
|---|---|---|
| Vulkan/Adreno | Vulkan port, typed evidence classes, QEMU/UNO Q gates | `vulkan_llvm` |
| CUDA | Processing port and CUDA ivshmem adapter | `cuda` |
| Knowledge | registry, selector, MDSOC/SPipe/wiki process updates | `metal_msl` |
| Merge/docs | requirements, architecture, integration, final review | root |

Shared names: `VulkanDevicePort`, `ProcessingDevicePort`,
`CudaHostOffloadAdapter`, `AdrenoTurnipAdapter`.

Manual steps: `Probe the GPU environment`; `Lower shared processing IR`;
`Submit through the selected Vulkan device`; `Verify device-origin readback`.

Merge owner and final high-capability reviewer: root. Sidecar findings require
root review before requirements, manuals, exclusions, or done marks are accepted.

