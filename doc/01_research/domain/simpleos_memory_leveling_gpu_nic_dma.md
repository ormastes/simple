<!-- codex-research -->
# GPU/NIC/DMA Memory Leveling Domain Research

## CPU and Tiered Memory

Linux Multi-Gen LRU separates aging from eviction, keeps a bounded generation
window, and uses refault feedback rather than rescanning every page on every
reclaim. SimpleOS should use small generation/candidate queues and incremental
counters, not a global hotness scan.

Source: https://docs.kernel.org/mm/multigen_lru.html

DAMON demonstrates sampled access monitoring with explicit region/time bounds.
SimpleOS does not need DAMON’s machinery initially, but its policy should accept
sampled access epochs and cap work per pressure cycle.

Source: https://docs.kernel.org/mm/damon/index.html

TPP shows that transparent tiering benefits from separating allocation from
promotion/demotion and from keeping hot pages in fast memory while colder pages
move to slower memory. Its CXL results support asymmetric high/low watermarks
and fault/access-driven promotion rather than symmetric periodic migration.

Source: https://arxiv.org/abs/2206.02878

## GPU Memory

Linux HMM represents device-private memory with normal page metadata and splits
migration into prepare, owner copy, commit, and finalize phases. Pinned pages are
excluded before migration. This directly supports a SimpleOS prepare/copy/
commit/rollback state machine owned jointly by VMM and the device driver.

Source: https://docs.kernel.org/6.7/mm/hmm.html

CUDA Unified Memory uses faults and access counters for placement and
thrashing mitigation, but coherency and oversubscription depend on hardware.
Therefore SimpleOS placement hints cannot imply simultaneous CPU/GPU access or
migration capability.

Source: https://docs.nvidia.com/cuda/cuda-programming-guide/04-special-topics/unified-memory.html

GPUVM explores NIC-assisted GPU paging and reports large gains for selected
latency-bound workloads. It is useful as a future owner backend, not a generic
first implementation: it depends on an RDMA-capable NIC and GPU-driven control.

Source: https://arxiv.org/abs/2411.05309

GPU oversubscription research consistently finds fault handling, eviction, and
thrashing dominant. A bounded rule-based policy with explicit anti-thrash
cooldown is preferable to adding an ML predictor before SimpleOS has real
access telemetry.

Sources:
- https://research.spec.org/icpe_proceedings/2022/proceedings/p67.pdf
- https://people.cs.pitt.edu/~debashis/papers/IPDPS2020.pdf

## DMA and NIC Memory

The Linux DMA API requires map/unmap pairing, transfer-direction preservation,
device-idle proof before unmap, and sync-for-CPU/device around streaming DMA.
These are ownership transitions, not optional cache hints.

Source: https://docs.kernel.org/6.3/core-api/dma-api-howto.html

Linux page-pool keeps NIC pages mapped and recycles them with reference and DMA
sync accounting. SimpleOS should protect a bounded NIC reserve and recycle ring
buffers instead of repeatedly registering/swapping them.

Source: https://www.kernel.org/doc/html/latest/networking/page_pool.html

FileMR and Firehose show why registration/pinning should be pooled and cached:
registration and NIC translation state are expensive and bounded resources.

Sources:
- https://www.usenix.org/system/files/nsdi20-paper-yang.pdf
- https://titanium.cs.berkeley.edu/papers/bell-bonachea-firehose.pdf

## Resulting Design Constraints

- One metadata record per allocation/range, with page-level detail only where
  VMM migration requires it.
- Bounded generation queues and bounded pressure batches.
- Explicit CPU-owned, device-owned, synchronizing, migrating, swapped, and
  failed states with prepare/commit/rollback.
- Pin count and in-flight DMA count, not booleans.
- Protected GPU/NIC/DMA reservations plus CPU and swap watermarks.
- Device-private movement only through a registered owner capability.
- Anti-thrash cooldown/refault counters before repeat promotion.

