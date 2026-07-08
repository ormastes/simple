# SimpleOS Memory Leveling

Status: profile-policy slice.

The current SimpleOS memory-leveling surface is a pure policy model in
`src/os/kernel/memory/memory_leveling.spl`. It does not move real pages yet.

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

Focused evidence:

```sh
bin/simple test test/03_system/os/simpleos_memory_leveling_spec.spl --mode=interpreter
```

Do not claim GPUDirect, RDMA hardware paging, CXL, or live GPU/NIC migration
from this model-only evidence.
