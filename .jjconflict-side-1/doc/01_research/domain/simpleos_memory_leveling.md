# SimpleOS Memory Leveling Domain Research

Status: draft domain research.

## Papers And Systems

### Linux HMM

Linux Heterogeneous Memory Management integrates device memory, such as GPU
on-board memory, into normal kernel memory paths with specialized `struct page`
support. This supports the key SimpleOS lesson: device memory should be modeled
as memory with page metadata, not as opaque runtime handles only.

Source: https://www.kernel.org/doc/html/v6.4/mm/hmm.html

### GPUDirect RDMA

NVIDIA GPUDirect RDMA allows PCIe peer devices, such as NICs or storage
adapters, to exchange data with GPU memory. The important OS contract is not
"GPU memory is swappable"; it is that peer DMA needs pinned, registered,
device-visible mappings with isolation.

Source: https://docs.nvidia.com/cuda/gpudirect-rdma/

### GPUVM / DREAM

GPUVM proposes GPU-driven unified virtual memory using an RDMA-capable NIC for
on-demand paging when GPU memory is oversubscribed. DREAM continues this line
with device-driven virtual-memory access. These papers are directly relevant
to the requested GPU+NIC model, but they are advanced hardware/offload targets,
not a first SimpleOS kernel slice.

Sources:
- https://arxiv.org/pdf/2411.05309
- https://dl.acm.org/doi/10.1145/3721145.3725748

### GPU Unified Memory Oversubscription

GPU oversubscription studies show page fault handling and host-to-device /
device-to-host migration dominate cost once GPU memory is full. Adaptive
schemes use runtime fault/migration behavior to pick policies for irregular
applications instead of blindly prefetching.

Sources:
- https://www.cs.sjtu.edu.cn/~lichao/publications/Oversubscribing_GPU_ICPE-2022-Shao.pdf
- https://people.cs.pitt.edu/~debashis/papers/IPDPS2020.pdf
- https://past.date-conference.com/proceedings-archive/2021/pdf/1974.pdf

### CXL / Tiered Memory

Nomad argues for non-exclusive tiering: keep shadow copies after promotion to
reduce thrash when fast memory is pressured. M5 and HybridTier show that page
hotness telemetry matters for good tiering. SimpleOS should keep a `shadowed`
state in the model, but avoid claiming real CXL until hardware evidence exists.

Sources:
- https://arxiv.org/html/2401.13154v2
- https://jiyuan.is/papers/asplos25-m5.pdf
- https://www.sihangliu.com/docs/hybridtier_asplos25.pdf

### RDMA Registration And Pinning

RDMA systems pay high costs for registration, pinning, and IOMMU mapping.
FileMR reports expensive on-demand paging for RNIC memory mappings; PART and
Firehose explore reducing or caching pinning overhead. SimpleOS should treat
NIC-registered and DMA-pinned pages as non-swappable until explicitly released,
and it should pool registrations rather than register in the hot path.

Sources:
- https://www.usenix.org/system/files/nsdi20-paper-yang.pdf
- https://psistakis.cs.illinois.edu/files/publications/psistakis-nocs20.pdf
- https://gasnet.lbl.gov/pubs/bell-bonachea-firehose.pdf

## Recommended Model

Use one OS-owned memory-leveling policy with explicit configuration profiles,
so bare-metal targets do not pay for a complex heterogeneous model:

- `baremetal_static`: fixed pools, no swap, no background migration, explicit
  DMA pin/release validation.
- `simpleos_default`: CPU DRAM plus optional block/file swap and cold-page
  demotion.
- `heterogeneous_device`: CPU DRAM, swap, GPU-resident pages, NIC/RDMA
  registered pages, DMA-pinned pages, and optional shadow copies.

Use explicit page states:

- `cpu_hot`: normal DRAM target.
- `cpu_cold`: demotion candidate.
- `swap_backed`: evictable to block/file swap.
- `gpu_resident`: GPU placement lease exists.
- `nic_registered`: RDMA/NIC memory registration exists.
- `dma_pinned`: device-visible DMA mapping exists.
- `shadowed`: fast-tier and slow-tier copies coexist.

Rules:

- DMA-pinned or NIC-registered pages are not swappable.
- GPU-resident pages require explicit CPU/GPU coherence state before migration.
- Shadow copies are allowed only when the owner state can prove freshness.
- A policy model may simulate GPU/NIC/CXL tiers before hardware exists, but
  user-facing evidence must label it as model evidence.
