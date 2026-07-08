# SimpleOS Memory Leveling

Status: profile-policy slice.

The current SimpleOS memory-leveling surface is a pure policy model in
`src/os/kernel/memory/memory_leveling.spl`. It does not move real pages yet.

Profiles:

- `baremetal_static`: fixed pools, no swap, no migration, DMA pin safety.
- `simpleos_default`: CPU DRAM plus optional swap/demotion for ordinary pages.
- `heterogeneous_device`: CPU, swap, GPU, NIC/RDMA, DMA-pinned, and shadow-copy
  policy states.

Safety rule: device-visible pages fail closed. DMA-pinned, NIC-registered, and
GPU-resident pages are not swappable in this slice.

Focused evidence:

```sh
bin/simple test test/03_system/os/simpleos_memory_leveling_spec.spl --mode=interpreter
```

Do not claim GPUDirect, RDMA hardware paging, CXL, or live GPU/NIC migration
from this model-only evidence.
