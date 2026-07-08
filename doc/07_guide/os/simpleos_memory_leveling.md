# SimpleOS Memory Leveling

Status: hardware-gated profile-policy slice.

The current SimpleOS memory-leveling surface is a pure policy model in
`src/os/kernel/memory/memory_leveling.spl`. It gates real hardware claims but
does not move GPU/NIC pages yet.

The Simple language-facing surface is `std.memory_leveling`. It represents
ownership/placement intent as pure data and does not add syntax.

Profiles:

- `baremetal_static`: fixed pools, no swap, no migration, DMA pin safety.
- `simpleos_default`: CPU DRAM plus optional swap/demotion for ordinary pages.
- `heterogeneous_device`: CPU, swap, GPU, NIC/RDMA, DMA-pinned, and shadow-copy
  policy states.

Safety rule: device-visible pages fail closed. DMA-pinned, NIC-registered, and
GPU-resident pages are not swappable in this slice.

Language-to-OS adapter:

- `simple_memory_iso_cpu_cold()` maps to an ordinary cold CPU page.
- `simple_memory_device_gpu()` maps to a GPU-resident page and rejects swap.
- `simple_memory_network_registered()` maps to NIC-registered memory.
- `simple_memory_dma_pinned()` maps to DMA-pinned memory.

Real hardware target gate:

- `simple_memory_x86_cpu_real()`, `simple_memory_arm_cpu_real()`, and
  `simple_memory_riscv_cpu_real()` apply the CPU page policy when marked with
  real evidence.
- `simple_memory_vulkan_gpu_real()`, `simple_memory_metal_gpu_real()`,
  `simple_memory_cuda_gpu_real()`, and `simple_memory_rdma_nic_real()` are
  recognized as real device-memory targets, but remain pinned/fail-closed.
- `simple_memory_vulkan_gpu_readback_real()` and
  `simple_memory_cuda_gpu_readback_real()` return `pin_device` when readback
  proof exists. `simple_memory_metal_gpu_readback_real()` is implemented but not
  tested in this lane.
- `memory_leveling_real_hardware_decide(profile, intent)` rejects model-only
  hardware claims with `real-hardware-evidence-required`.

Focused evidence:

```sh
bin/simple test test/03_system/os/simpleos_memory_leveling_spec.spl --mode=interpreter
```

Do not claim GPUDirect, RDMA hardware paging, CXL, or live GPU/NIC migration
from this hardware-gated policy. Real device movement still needs driver-owned
migration/coherence evidence.
