Awesome—here’s your **Path-B** doc updated with a crisp “address space” model and code that tracks each address form:

---

# Address vocabulary (what each address *actually* is)

| Name (variable)                                 | Who uses it                         | What it is                                                      | How you get it                                                         | Where it’s valid                                                |
| ----------------------------------------------- | ----------------------------------- | --------------------------------------------------------------- | ---------------------------------------------------------------------- | --------------------------------------------------------------- |
| **host_local** (`void*`)                        | CPU code (your userspace)           | CPU **virtual** address                                         | `posix_memalign`, `malloc`, etc.                                       | Only the CPU; **not** valid for DMA                             |
| **physical_address** (`phys_addr_t`/`uint64_t`) | Kernel/MMIO docs, NVMe spec wording | System **physical RAM** address (or MMIO physical)              | Kernel knows; user-space usually **doesn’t**                           | Not directly programmed to devices when an **IOMMU** is present |
| **pci_address** (`uint64_t`)                    | CPU when hitting device registers   | **MMIO bus** address (BAR + offset) for NVMe regs/doorbells     | Map BAR via VFIO, then CPU writes                                      | Valid for **MMIO** (doorbells/regs), not for data buffers       |
| **iova_address** (`dma_addr_t`/`uint64_t`)      | **Device DMA** (NVMe controller)    | **IO Virtual Address** in device’s IOMMU domain (“DMA address”) | VFIO `VFIO_IOMMU_MAP_DMA` for host RAM; **peer-mem shim** for GPU VRAM | Program this into **ASQ/ACQ**, **PRP/SGL**, etc.                |
| **device_local** (`CUdeviceptr`)                | GPU                                 | **GPU virtual** address                                         | `cuMemAlloc`                                                           | Only the GPU; not CPU/DMA usable                                |

Why this matters:

* Linux distinguishes **CPU virtual**, **CPU physical**, and **bus/DMA** addresses. Devices do DMA using **bus/DMA** addresses; with an IOMMU that means **IOVA** (what you program) → translated to physical behind the scenes. ([리눅스 커널 문서][1])
* VFIO maps **CPU memory** to **IOVA** for the device. ([리눅스 커널 문서][2])
* Your GPU pointer is a **GPU VA**; to make it usable by NVMe you need a kernel shim that turns it into **NVMe-valid DMA addresses** (IOVAs) via NVIDIA GPUDirect RDMA peer APIs and DMA-mapping. ([NVIDIA Docs][3])
* NVMe spec text says “**physical address**” for ASQ/ACQ and PRPs; in IOMMU systems you actually program the **DMA/IOVA** that the controller uses, and the IOMMU translates to physical. (Spec sections: ASQ/ACQ base, PRP entries, DSTRD.) ([portal.beam.ltd.uk][4])

---

# Step table (with address forms per step)

| # | Goal                                   | APIs / actions                                                                                 | Address you handle                                                                                                                  |
| - | -------------------------------------- | ---------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| 0 | Bring device to VFIO + IOMMU           | Bind NVMe to `vfio-pci`; enable VT-d/AMD-Vi                                                    | (no buffers yet) — sets up IOMMU domain. ([리눅스 커널 문서][2])                                                                           |
| 1 | Map **host RAM** for queues/PRP list   | Allocate page-aligned host buffer → `VFIO_IOMMU_MAP_DMA`                                       | **host_local** (CPU VA), **iova_address** (for device) ([리눅스 커널 문서][1])                                                             |
| 2 | Allocate **GPU VRAM** for data         | `cuMemAlloc` → returns **device_local** (`CUdeviceptr`)                                        | **device_local** only (GPU VA)                                                                                                      |
| 3 | Turn GPU VA → **NVMe-usable IOVAs**    | Kernel shim: `nvidia_p2p_get_pages` + `nvidia_p2p_dma_map_pages` (map for the **NVMe** device) | returns **iova_address** segments for VRAM (plus lengths) ([NVIDIA Docs][3])                                                        |
| 4 | Build **PRP/SGL** for READ             | Put PRP list in **host RAM** (step 1) and fill with **GPU IOVAs** (step 3)                     | PRP entries are **iova_address** values; list itself has **host_local**/**iova_address**. Spec PRP rules. ([portal.beam.ltd.uk][4]) |
| 5 | Post cmd to **I/O SQ** & ring doorbell | Write SQE into SQ (host RAM) → write DB in BAR via MMIO                                        | SQ/CQ **host_local**/**iova_address**; doorbell uses **pci_address** (BAR0+offset, uses DSTRD) ([portal.beam.ltd.uk][4])            |
| 6 | **Admin ASQ/ACQ** base                 | Program **ASQ/ACQ** with **IOVA** of host queues (not GPU)                                     | **iova_address** for ASQ/ACQ. Spec fields say “physical”, but use DMA/IOVA. ([portal.beam.ltd.uk][4])                               |

> P2P topology caveat: GPU and NVMe should share a PCIe root complex/switch for peer DMA to succeed (P2PDMA docs). ([리눅스 커널 문서][5])

---

# Drop-in code with address variables

### A) VFIO map for queues + PRP list (host RAM → IOVA)

```c
// allocate host queue/PRP pages
void* host_local = nullptr;
size_t host_len = 1UL << 20;                 // 1 MiB
posix_memalign(&host_local, 4096, host_len);

// map to device IOVA via VFIO
struct vfio_iommu_type1_dma_map map = {
  .argsz = sizeof(map),
  .flags = VFIO_DMA_MAP_FLAG_READ | VFIO_DMA_MAP_FLAG_WRITE,
  .iova  = 0x7000000000ULL,                  // choose free IOVA
  .vaddr = (uintptr_t)host_local,
  .size  = host_len
};
ioctl(vfio_container, VFIO_IOMMU_MAP_DMA, &map);

uint64_t prp_list_iova = map.iova;           // <-- iova_address (device/DMA)
uint64_t pci_bar0 = nvme_bar0_phys;          // <-- pci_address base (BAR0)
```

* `host_local` = CPU VA, `prp_list_iova` = IOVA the **NVMe** uses, `pci_bar0` = BAR address you `mmap()` and then use offsets for doorbells (stride per **CAP.DSTRD**). ([리눅스 커널 문서][1])

### B) GPU buffer + kernel shim → IOVA segments

```c
// CUDA device buffer (GPU VA)
CUdeviceptr device_local = 0;                // <-- device_local
size_t gpu_len = 128UL << 20;                // 128 MiB
cuMemAlloc(&device_local, gpu_len);

// Ask kernel shim to map GPU VA -> NVMe IOVAs
gpu_p2p_map_req req = {0};
req.gpu_va = (uint64_t)device_local;
req.size   = gpu_len;
req.domain = 0; req.bus = 0x5e; req.devfn = (0x00<<3)|0; // NVMe BDF

ioctl(shim_fd, GPU_P2P_MAP, &req);

// Now req.segs[i] are { iova_address, len } in NVMe’s IOMMU domain
uint64_t first_gpu_iova = req.segs[0].iova;  // <-- iova_address (for PRP1)
```

* Kernel shim uses **GPUDirect RDMA** peer APIs to pin GPU pages and produce **NVMe-valid DMA** addresses. ([NVIDIA Docs][3])

### C) Build PRPs that point into **GPU IOVAs**, post command, ring doorbell

```c
// PRP list lives in host RAM (CPU-visible), but entries are GPU IOVAs
uint64_t* prp_list = (uint64_t*)host_local;  // PRP list buffer (first part)
size_t prp_cnt = 0;

size_t page = 4096;                          // CC.MPS page size, often 4K
size_t nbytes = nlb * lba_size;

// PRP1 may have offset inside first page
uint64_t first_offset = 0;                   // example: aligned
uint64_t prp1 = first_gpu_iova + first_offset;

size_t consumed = page - ((size_t)prp1 & (page-1));
nbytes -= (consumed == page ? 0 : consumed);

// fill PRP list with subsequent page-aligned GPU IOVAs
for (unsigned s = 0; s < req.out_nsegs && nbytes; ++s) {
  uint64_t base = req.segs[s].iova;
  uint64_t len  = req.segs[s].len;
  if (s == 0) { base += consumed; len -= consumed; }
  for (uint64_t p = 0; p < len && nbytes; p += page) {
    prp_list[prp_cnt++] = base + p;          // <-- each entry is an IOVA page in GPU VRAM
    nbytes -= nbytes > page ? page : nbytes;
  }
}

// NVMe READ SQE
struct NvmeCmd { /* ... fields incl. prp1/prp2 ... */ } cmd = {0};
cmd.opc  = 0x02;                             // READ
cmd.nsid = nsid;
cmd.slba = start_lba;
cmd.nlb  = nlb - 1;
cmd.prp1 = prp1;                             // IOVA into GPU VRAM
cmd.prp2 = prp_list_iova;                    // IOVA of PRP list (host RAM)

// write SQE then ring doorbell via MMIO:
// doorbell = (volatile uint32_t*)(bar0_mmap + DB_OFF_SQ(qid, CAP.DSTRD));
*sq_tail_slot = cmd;
*sq_tail_db   = (tail+1) & (qdepth-1);
```

* PRP rules (alignment, PRP list chaining) are per NVMe Base Spec §4.3; DSTRD (doorbell stride) in **CAP** defines DB offsets. ([portal.beam.ltd.uk][4])

### D) Admin queue base addresses (what you actually program)

```c
// Admin queues should be in host RAM (CPU can read/write):
void* asq_host = aligned_alloc(4096, asq_bytes);
void* acq_host = aligned_alloc(4096, acq_bytes);

// Map them to IOVA for the device
map.vaddr = (uintptr_t)asq_host; map.size = asq_bytes; map.iova = 0x7100'000000ULL;
ioctl(vfio_container, VFIO_IOMMU_MAP_DMA, &map);
uint64_t ASQ_iova = map.iova;

map.vaddr = (uintptr_t)acq_host; map.size = acq_bytes; map.iova = 0x7200'000000ULL;
ioctl(..., VFIO_IOMMU_MAP_DMA, &map);
uint64_t ACQ_iova = map.iova;

// Program ASQ/ACQ registers (spec names say “physical address”;
// in an IOMMU setup you program the DMA/IOVA here).
mmio64(bar0 + ASQ_OFF) = ASQ_iova;          // Admin Submission Queue Base
mmio64(bar0 + ACQ_OFF) = ACQ_iova;          // Admin Completion Queue Base
```

* Spec registers: **ASQ** at offset 28h and **ACQ** at 30h; both require page alignment and are described as 64-bit “physical” base addresses—supply the **IOVA** you mapped. ([portal.beam.ltd.uk][4])

---

## Quick mental model

* **You always program the controller with DMA/IOVA** (what the device sees). Linux DMA-API calls this a `dma_addr_t`. On IOMMU systems, that IOVA is translated to **physical** automatically. ([리눅스 커널 문서][1])
* **Queues & PRP list pages** live in **host RAM** (easy for CPU to touch) → mapped to IOVA via **VFIO**.
* **Data buffers** can live in **GPU VRAM** → mapped to IOVA via your **peer-mem kernel shim**. ([NVIDIA Docs][3])
* **Doorbells/regs** are **MMIO** (BAR space) → accessed by CPU at a mapped **pci_address**, not DMA. DSTRD tells you the per-queue doorbell stride. ([portal.beam.ltd.uk][4])

If you want, I can fold these snippets into your current repo layout (shim header, ioctl IDs, VFIO bring-up, and a tiny “READ 4 MiB into VRAM” test) with your exact BDF and queue sizes.

[1]: https://docs.kernel.org/core-api/dma-api-howto.html "Dynamic DMA mapping Guide — The Linux Kernel  documentation"
[2]: https://docs.kernel.org/driver-api/vfio.html?utm_source=chatgpt.com "VFIO - “Virtual Function I/O”"
[3]: https://docs.nvidia.com/cuda/gpudirect-rdma/?utm_source=chatgpt.com "1. Overview — GPUDirect RDMA 13.0 documentation"
[4]: https://portal.beam.ltd.uk/support/dune/files/info//NVM-Express-1_4-2019.06.10-Ratified.pdf "Non-Volatile Memory Express"
[5]: https://docs.kernel.org/driver-api/pci/p2pdma.html?utm_source=chatgpt.com "PCI Peer-to-Peer DMA Support"
