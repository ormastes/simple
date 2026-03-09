# Address Space Reference

This document provides a comprehensive reference for understanding different address spaces in GPU-NVMe interaction systems.

---

## Overview: The Address Spaces (Who Sees What)

Understanding the distinction between different address spaces is critical for GPU-NVMe integration. Each component (CPU, GPU, NVMe device, IOMMU) has its own view of memory addresses.

| Address Space Type | What It Really Is | Who Uses It | Notes / How It's Formed |
|--------------------|-------------------|-------------|------------------------|
| **CPU Virtual Address (VA)** | CPU process virtual address | Your userspace code on the CPU | Translated by the CPU MMU into system physical pages. Must be pinned (page-locked) for DMA. |
| **Physical Address (PA)** | System Physical Address | RAM as seen by the platform | Devices rarely see raw PA when an **IOMMU** is enabled. |
| **I/O Virtual Address (IOVA)** | Device DMA address | What a PCIe device *actually* DMAs to/from | Kernel maps memory into an IOMMU domain and returns a `dma_addr_t` (IOVA). Device uses IOVA; IOMMU translates to PA. |
| **GPU Virtual Address (GPU-VA)** | GPU virtual address for allocations like `cudaMalloc` | The GPU | Managed by the GPU's MMU; not equal to CPU VA; **not a DMA address** by default. Unified Virtual Addressing unifies pointer visibility, not DMAability. |
| **PCI/MMIO Address** | Two things: (1) MMIO/BAR addresses CPU uses for device registers; (2) bus DMA addresses on PCIe transactions | CPU for MMIO; devices for DMA | BARs are mapped into CPU VA for MMIO (doorbells, etc.). DMA addresses given to devices are **IOVAs** on IOMMU systems. |

---

## Rule of Thumb

**PRP/SGL entries and queue base addresses must carry *device-visible DMA addresses*** (IOVA on IOMMU systems, PA on systems without IOMMU). Always use what the Linux DMA API (`dma_map_*`) returns (`dma_addr_t`).

Reference: [Linux Kernel DMA API](https://www.kernel.org/doc/html/latest/core-api/dma-api.html)

---

## Physical Address vs IOVA — Relationship and When to Use Which

### Relationship

* **IOMMU translates IOVA → PA** during DMA transactions
* If there's **no IOMMU**, the **DMA address equals PA**
* If **SWIOTLB** is needed (e.g., addressing limits), the kernel may bounce via an intermediate buffer, but you still hand the device the `dma_addr_t` returned by the API

### What to Put in NVMe Fields

**Always use the device DMA address** (`dma_addr_t`):
* With IOMMU **enabled**: use **IOVA** (obtained from `VFIO_IOMMU_MAP_DMA` or kernel DMA API)
* With IOMMU **disabled**: use **PA** (the DMA API still returns the correct address)
* **Never** put CPU VA or GPU-VA in NVMe PRP/SGL/queue base fields

Reference: [Linux Kernel DMA Documentation](https://www.kernel.org/doc/Documentation/core-api/dma-api.rst)

---

## GPU-Resident Queues/Commands/Data (Profiles)

Mode 5 (current implementation): SQ + CQ in host RAM (controller-provisioned), data buffer in GPU VRAM (P2P), shadow doorbells in GPU VRAM.

| Object / Page         | Controller DMA (IOVA/PA)  | GPU VA              | CPU VA (if mapped) | Physical (if no IOMMU) | Notes |
|-----------------------|---------------------------|---------------------|--------------------|------------------------|-------|
| **SQ.page0/page1**    | Host IOVA (admin create)  | CUDA alias only     | Host queue memory  | `= DMA`                | SQ on host |
| **CQ.page0/page1**    | Host IOVA (admin create)  | CUDA alias only     | Host queue memory  | `= DMA`                | CQ on host |
| **PRP.list**          | Host IOVA (built on host) | CUDA alias only     | Host PRP memory    | `= DMA`                | Built on host |
| **Data pages**        | GPU IOVA (P2P)            | GPU buffer (pool)   | —                  | `= DMA`                | GPU-only buffer |
| **Buffer pool meta**  | GPU IOVA (pool export)    | GPU pool metadata   | —                  | `= DMA`                | Allocator state |
| **Shadow DB**         | — (shadow buffer)         | GPU VRAM            | Host alias (debug) | —                      | Daemon rings MMIO |
| **MMIO DB**           | — (BAR)                   | —                   | `BAR0+offset`      | BAR maps to PA         | Real doorbell |

> CQ remains host-resident until queues are re-provisioned via admin Create CQ/SQ with GPU PRPs (P2P/DBC). Data buffers are GPU-only (Mode 5) and require P2P; host bounce is disabled.

Mode 5 (target layout, CQ on GPU; requires queue reprovision with GPU PRPs):

| Object / Page         | Controller DMA (IOVA/PA) | GPU VA              | CPU VA (if mapped) | Physical (if no IOMMU) | Notes |
|-----------------------|--------------------------|---------------------|--------------------|------------------------|-------|
| **SQ.page0/page1**    | `0x0000_8100_0000`       | CUDA alias only     | Host queue memory  | `= DMA`                | SQ stays on host for MMIO doorbell |
| **CQ.page0/page1**    | `0x0000_9100_0000`       | `0x1400_1100_0000`  | Optional alias     | `= DMA`                | CQ mapped into GPU VRAM |
| **PRP.list**          | `0x0000_8200_0000`       | CUDA alias only     | Host PRP memory    | `= DMA`                | Built on host |
| **Data pages**        | `0x0000_9800_0000`       | `0x1400_2000_0000`  | —                  | `= DMA`                | GPU buffer pool (P2P) |
| **Buffer pool meta**  | `0x0000_9810_0000`       | `0x1400_2100_0000`  | —                  | `= DMA`                | GPU allocator state |
| **Shadow DB**         | — (shadow buffer)        | `0x1400_1200_0000`  | Host alias (debug) | —                      | Daemon rings MMIO |
| **MMIO DB**           | — (BAR)                  | —                   | `BAR0+offset`      | BAR maps to PA         | Real doorbell |

> Target table shows example addresses for a CQ placed in GPU VRAM; implementing this requires admin Create CQ/SQ with GPU PRPs via P2P/DBC support.

### PA ↔ IOVA Relationship (What to Fill Where)

* **With IOMMU enabled**: Devices never see raw PA; they see **IOVA**. You always put **IOVA** into NVMe queue base addresses and PRP/SGL entries; the IOMMU translates IOVA→PA at DMA time.
* **Without IOMMU**: The **DMA address equals PA** ("bus/physical"); you then place **PA** in PRP/SGL and queue base fields. The kernel DMA API still abstracts this via `dma_map_*` returning a `dma_addr_t`.

---

## When Do I Use Physical vs IOVA? (Cheat Sheet)

* **Use IOVA (the DMA address) everywhere** if the platform has an **IOMMU** (typical on modern servers). The Linux DMA API's `dma_map_single/dma_map_page` returns a `dma_addr_t` (the device-visible DMA address = IOVA). Put that value in **NVMe PRP/SGL** and **Create SQ/CQ** base fields.

* **Use PA** only on systems **without IOMMU** (or for devices/buses that bypass it). In that case `dma_addr_t` happens to equal PA, so the same rule ("use what `dma_map_*` returned") still holds.

* **GPU buffers**: When registered through **GDS/pci_p2pdma**, the kernel produces **device-valid IOVAs that map to GPU pages**; those IOVAs go into PRP/SGL so the NVMe can DMA directly to VRAM.

Reference: [Linux PCI Peer-to-Peer DMA](https://docs.kernel.org/driver-api/pci/p2pdma.html)

---

## How This Maps to NVMe

* **Queues (SQ/CQ)**: Live in **host memory** and are given to the controller via **queue base DMA addresses** (IOVA/PA). CPU rings doorbells via MMIO. Putting queues in GPU VRAM isn't supported in mainstream stacks.

* **Data payload**: Addresses go in **PRP/SGL** fields and must be **device DMA addresses**. PRPs point to 4 KiB pages and may chain.

* **Peer-to-peer (P2P) DMA**: Enables direct NVMe↔GPU transfers when topology and software allow (same root/switch, ACS/ATS rules). Linux provides **pci_p2pdma** for this path.

Reference: [NVMe Base Specification](https://nvmexpress.org/specifications/)

---

## Can Each Part Live in GPU Memory?

| Component | In GPU VRAM? | Optimal Location | Rationale |
|-----------|:------------:|------------------|-----------|
| **Admin/IO Submission Queue (SQ)** | ⚠️ Possible | **Host RAM** | CPU/GPU writes commands; CPU rings doorbells via MMIO. Host memory provides lowest latency for CPU doorbell writes. |
| **Completion Queue (CQ)** | ⚠️ Possible | **Host RAM** | CPU must poll completions. Reading from GPU VRAM over PCIe adds latency. Host memory enables efficient CPU polling. |
| **Command's PRP list** | ⚠️ Possible | **Host RAM** | Small structure (<4KB) built per command by CPU. No benefit from GPU placement; host memory simplifies management. |
| **Data buffer** | ✅ Yes | **GPU VRAM** | Via **GDS/pci_p2pdma**: Direct NVMe→GPU DMA eliminates host bounce buffer, minimizes PCIe traffic, enables immediate GPU processing. |
| **Buffer Pool Metadata** | ✅ Yes | **GPU VRAM** | GPU manages buffer allocation/freeing. Keeping metadata in VRAM avoids CPU←→GPU synchronization overhead. |

**Performance Summary:**
- **SQ/CQ/PRP in Host RAM**: Optimizes CPU command submission and completion polling paths
- **Data buffers in GPU VRAM**: Eliminates bounce buffers, enables direct NVMe↔GPU data path
- **Result**: Best of both worlds—fast CPU control plane, zero-copy GPU data plane

**Note:** NVMe **CMB/PMR** are controller-local; useful but not GPU memory.

---

## Optimal Memory Placement Strategy

### Design Principle: Split Control Plane and Data Plane

**Control Plane (Host RAM):**
- Submission Queues (SQ)
- Completion Queues (CQ)
- PRP Lists
- Command metadata

**Data Plane (GPU VRAM):**
- Data buffers
- Buffer pool metadata
- GPU-managed state

**Module 57 Mode 5 (Current Implementation):**
- SQ: Host RAM (device queue created by admin commands)
- CQ: Host RAM (controller provisioning still host-side; GPU reads via CUDA alias)
- Data buffers: GPU VRAM only (P2P required; host bounce disabled)
- Doorbells: Shadow buffer in GPU VRAM, daemon rings real MMIO
- To move CQ into GPU VRAM, the IO queue must be recreated via admin Create CQ/SQ using GPU PRPs exported through P2P/DBC; not yet implemented.

**Mode 5 Target vs Current**
- Target: SQ host, CQ GPU, data buffers GPU, buffer pool metadata GPU.
- Current gap: CQ remains host-provisioned; controller DMA still lands in host memory. Fix requires admin queue re-provisioning with GPU PRPs (P2P/DBC) and controller support for GPU-backed queues.

### Why This Split?

#### 1. Submission Queue in Host RAM

```
CPU Command Submission Flow:
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│ Build SQE    │ ──→ │ Write to SQ  │ ──→ │ Ring DB      │
│ (CPU)        │     │ (Host RAM)   │     │ (MMIO write) │
└──────────────┘     └──────────────┘     └──────────────┘
   ~10 cycles           ~100 cycles          ~1000 cycles

Alternative (SQ in GPU VRAM):
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│ Build SQE    │ ──→ │ PCIe write   │ ──→ │ Ring DB      │
│ (CPU)        │     │ to GPU VRAM  │     │ (MMIO write) │
└──────────────┘     └──────────────┘     └──────────────┘
   ~10 cycles           ~500 cycles          ~1000 cycles
```

**Verdict**: Host RAM saves ~400 cycles per command submission.

#### 2. Completion Queue in Host RAM

```
CPU Completion Polling:
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│ Read CQE     │ ──→ │ Check Phase  │ ──→ │ Process      │
│ (Host RAM)   │     │ (CPU cache)  │     │ (CPU)        │
└──────────────┘     └──────────────┘     └──────────────┘
   ~100 cycles          ~10 cycles           ~50 cycles

Alternative (CQ in GPU VRAM):
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│ PCIe read    │ ──→ │ Check Phase  │ ──→ │ Process      │
│ from GPU     │     │ (uncached)   │     │ (CPU)        │
└──────────────┘     └──────────────┘     └──────────────┘
   ~500 cycles          ~500 cycles          ~50 cycles
```

**Verdict**: Host RAM saves ~900 cycles per completion + enables CPU cache-friendly polling.

#### 3. PRP List in Host RAM

- **Size**: Typically <4KB (512 PRP entries × 8 bytes)
- **Builder**: CPU constructs PRP list from buffer addresses
- **Usage**: NVMe controller DMAs PRP list once per command
- **Benefit of GPU placement**: None (NVMe reads it once, CPU builds it)
- **Cost of GPU placement**: Extra PCIe write from CPU to GPU

**Verdict**: Host RAM is simpler and faster.

#### 4. Data Buffers in GPU VRAM

```
Host-Pinned Path (Modules ≤54):
NVMe ──DMA──→ Host RAM ──PCIe read──→ GPU ──Process──→ GPU VRAM
        ~1 GB/s           ~12 GB/s         ~1000 GB/s

GPU-Direct Path (Modules ≥55):
NVMe ──────────DMA (P2P)──────────→ GPU VRAM ──Process──→ (in-place)
                ~3 GB/s                      ~1000 GB/s
```

**Verdict**: GPU VRAM eliminates one PCIe transfer, doubles effective bandwidth.

#### 5. Buffer Pool Metadata in GPU VRAM

```
GPU Buffer Allocation:
┌──────────────┐     ┌──────────────┐     ┌──────────────┐
│ GPU kernel   │ ──→ │ Read pool    │ ──→ │ Allocate     │
│ needs buffer │     │ metadata     │     │ (atomic op)  │
└──────────────┘     └──────────────┘     └──────────────┘

If metadata in Host RAM:
  - PCIe roundtrip: ~1000 cycles
  - CPU sync overhead: potential bottleneck

If metadata in GPU VRAM:
  - GPU atomic: ~100 cycles
  - No CPU involvement: scales to many GPU threads
```

**Verdict**: GPU VRAM enables efficient GPU-driven buffer management.

### Performance Impact Summary

| Component | Host RAM Latency | GPU VRAM Latency | Optimal Location |
|-----------|------------------|------------------|------------------|
| **SQ write + doorbell** | ~1100 cycles | ~1500 cycles | Host RAM |
| **CQ poll** | ~160 cycles | ~1000 cycles | Host RAM |
| **PRP build** | ~200 cycles | ~700 cycles | Host RAM |
| **Data transfer** | 2× PCIe (bounce) | 1× PCIe (direct) | GPU VRAM |
| **Buffer alloc (GPU)** | ~1000 cycles | ~100 cycles | GPU VRAM |

**Total Speedup**: 2-3× for typical I/O workloads (command submission + data transfer + processing)

### Alternative Placements (Advanced)

#### GPU-Initiated Commands (Future Work)

If GPU kernels submit NVMe commands directly:
- **SQ in GPU VRAM**: Reduces GPU→Host PCIe write latency
- **Doorbell Shadow Buffer**: GPU writes to VRAM, CPU daemon rings actual doorbell
- **Trade-off**: Adds CPU daemon latency but enables massive GPU-side parallelism

See: [Module 56: GPU Queue with GPU Buffer](../56.GPU_Queue_GPU_Buffer/README.md)

#### Hybrid CQ Processing

- **Primary CQ in Host RAM**: CPU polls for fast path
- **Secondary CQ in GPU VRAM**: GPU kernel polls for GPU-initiated commands
- **Complexity**: Requires careful queue management and synchronization

---

## GPU Buffer Profiles (Default vs Legacy)

**Default GPU Buffer (Optimal Placement — now the standard):**
- **SQ / CQ**: Host RAM (pinned + IOVA) for low-latency CPU doorbells and polling
- **PRP list**: Host RAM; CPU builds once, NVMe reads once
- **Data buffer**: GPU VRAM (GPUDirect/P2P) to remove host bounce buffer
- **Buffer pool metadata**: GPU VRAM to keep GPU allocation cheap
- **Used by**: Modules 53, 56, 57, 58, 59 (performance path)

**Naive GPU Buffer (Legacy all-in-GPU):**
- **SQ / CQ / PRP / data / pool**: GPU VRAM
- **Used by**: Module 56 legacy experiments; higher host doorbell/poll latency

**Rule of thumb:** Start with the **Default GPU Buffer**; fall back to **Naive** only when explicitly testing GPU-resident queue mechanics.

---

## Two Supported Paths for NVMe → GPU

### A) GPUDirect Storage (GDS)

Kernel NVMe driver owns the device; your application uses **cuFile** to register GPU buffers and issue file I/O; the stack provides **IOVAs** that map to GPU pages so the NVMe can DMA directly.

Reference: [NVIDIA GPUDirect Storage](https://docs.nvidia.com/gpudirect-storage/)

### B) VFIO (+ pci_p2pdma)

Bind NVMe to `vfio-pci`, create queues in pinned host memory, map them to **IOVAs**; for GPU buffers, rely on kernel support to obtain **IOVAs for GPU pages** (pci_p2pdma/GDS). Pure userspace mapping of GPU VRAM for an NVMe's IOMMU domain isn't viable without kernel support.

**Topology constraints:** NVMe and GPU must share a P2P-capable path (root port/switch; ACS). Otherwise, transfers may fail or fall back.

Reference: [Linux PCI P2P Documentation](https://docs.kernel.org/driver-api/pci/p2pdma.html)

---

## Applying This to Your Pipeline

> `create_queue()` → **command queue** → **NVMe read command** → **PRP** → **buffer** → **CUDA device memory**

* **Queues in host memory**, exposed by **IOVA** to the controller
* **PRP list in host memory**; **PRP entries** point to **device DMA addresses** of the data pages. If data is in GPU VRAM, those are **IOVAs that map to GPU pages** (via GDS/pci_p2pdma)
* **Data buffer** is your `cudaMalloc` region **registered for DMA** so the controller can DMA directly to it

---

## Admin Privileges Required

Enabling IOMMU, binding NVMe to `vfio-pci`, mapping DMA regions, and MMIO access from userspace require **root**. Installing/enabling GDS and p2pdma also requires admin control.

---

## Quick Mental Model (Cheat Sheet)

* **CPU VA → PA** via CPU MMU
* **Device DMA address (IOVA) → PA** via IOMMU; always use the **`dma_addr_t`** returned by the DMA API in NVMe fields
* **`cudaMalloc` → GPU-VA** (not a DMA address) until registered for GDS/P2P so the kernel can provide **IOVAs** for those GPU pages

---

## Address Translation Flow

### With IOMMU Enabled (Typical)

```
┌─────────────────────────────────────────────────────────────┐
│ User Space                                                  │
│  1. malloc/cudaMalloc → CPU-VA / GPU-VA                     │
│  2. VFIO_IOMMU_MAP_DMA → Creates IOVA mapping               │
└───────────────────────────────┬─────────────────────────────┘
                                │
                                ↓
┌─────────────────────────────────────────────────────────────┐
│ IOMMU                                                       │
│  IOVA → Physical Address (transparent translation)          │
└───────────────────────────────┬─────────────────────────────┘
                                │
                                ↓
┌─────────────────────────────────────────────────────────────┐
│ NVMe Controller                                             │
│  DMA using IOVA addresses from PRP/SGL/queue base           │
└─────────────────────────────────────────────────────────────┘
```

### Without IOMMU (Legacy)

```
┌─────────────────────────────────────────────────────────────┐
│ User Space                                                  │
│  1. malloc → CPU-VA                                         │
│  2. DMA API → Returns PA (no translation layer)             │
└───────────────────────────────────┬─────────────────────────┘
                                │
                                ↓
┌─────────────────────────────────────────────────────────────┐
│ NVMe Controller                                             │
│  DMA directly using Physical Addresses                      │
└─────────────────────────────────────────────────────────────┘
```

---

## References

1. [Linux Kernel DMA API](https://www.kernel.org/doc/html/latest/core-api/dma-api.html) - Dynamic DMA mapping
2. [Linux Kernel DMA Documentation](https://www.kernel.org/doc/Documentation/core-api/dma-api.rst)
3. [PCI Peer-to-Peer DMA Support](https://docs.kernel.org/driver-api/pci/p2pdma.html)
4. [x86 IOMMU Support](https://docs.kernel.org/arch/x86/iommu.html)
5. [NVIDIA GPUDirect Storage API](https://docs.nvidia.com/gpudirect-storage/api-reference-guide/index.html)
6. [Linux PCI Driver API](https://docs.kernel.org/driver-api/pci/index.html)
7. [NVMe Base Specification](https://nvmexpress.org/specifications/)
