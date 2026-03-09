Here’s a compact, **Path-B (VFIO + kernel peer-mem shim)** checklist you can follow. I split it into the exact steps you asked for and added the “admin/SQ/CQ in GPU memory?” bit at the end.

---

### NVMe→GPU VRAM DMA (userspace driver) — step-by-step

| # | Goal                                                      | Do it in                        | Root?           | What to use                                                   | Minimal code/command                                                                                                                                                                                                                                   | Notes                                                                                                                                                 |                                                    |                                                                                   |
| - | --------------------------------------------------------- | ------------------------------- | --------------- | ------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------- | --------------------------------------------------------------------------------- |
| 0 | Bind NVMe to **vfio-pci** and enable IOMMU                | shell                           | ✅ (one-time)    | Linux VFIO + IOMMU                                            | ```bash\n sudo grubby --update-kernel=ALL --args="intel_iommu=on iommu=pt"\n BDF=0000:5e:00.0; echo $BDF                                                                                                                                                 | sudo tee /sys/bus/pci/drivers/nvme/unbind\n VID=$(cat /sys/bus/pci/devices/$BDF/vendor); DID=$(cat /sys/bus/pci/devices/$BDF/device)\n echo "$VID $DID" | sudo tee /sys/bus/pci/drivers/vfio-pci/new_id\n ``` | Sets the device up for userspace control via VFIO’s TYPE1 IOMMU. ([리눅스 커널 문서][1]) |
| 1 | **IOVA map (for queues/PRP list in host RAM)**            | userspace                       | ❌               | VFIO ioctls                                                   | Map a host buffer so the **controller** can DMA it:  \n `c\n struct vfio_iommu_type1_dma_map m={.argsz=sizeof(m),.flags=3,.iova=IOVA,.vaddr=(uintptr_t)buf,.size=len};\n ioctl(vfio_container, VFIO_IOMMU_MAP_DMA, &m);\n `                                | VFIO maps **CPU memory** ↔ IOVA; this is perfect for **SQ/CQ** and PRP lists. ([리눅스 커널 문서][1])                                                        |                                                    |                                                                                   |
| 2 | Get a **GPU buffer** to hold data                         | userspace                       | ❌               | CUDA Driver API                                               | `c\n cuInit(0); cuCtxCreate(&ctx,0,dev);\n CUdeviceptr dptr; cuMemAlloc(&dptr, bytes);\n `                                                                                                                                                                | Gets you a **device pointer** (GPU VA). Not CPU-mappable.                                                                                             |                                                    |                                                                                   |
| 3 | **Translate GPU VA → DMA (IOVA) segments usable by NVMe** | kernel (shim) + userspace ioctl | ✅ (module load) | NVIDIA **GPUDirect RDMA** peer-mem API in a **kernel module** | Kernel side (sketch):  \n `c\n nvidia_p2p_get_pages(..., gpu_va, len, &pt,...);\n nvidia_p2p_dma_map_pages(nvme_pci_dev, pt, &dm);\n // return dm->dma_addresses[] as {iova,len} to userspace\n `\n Userspace: `ioctl(/dev/gpu_p2p_nvme, GPU_P2P_MAP, &req)` | VFIO cannot map CUDA pointers; you need the peer-mem shim to create **NVMe-valid DMA addresses** for VRAM. ([NVIDIA Docs][2])                         |                                                    |                                                                                   |
| 4 | Make a **PRP/SGL** that points to the GPU segments        | userspace                       | ❌               | NVMe spec PRP rules                                           | Build PRP1/PRP2 (PRP list in **host RAM** you mapped in step 1):  \n `c\n prp1 = gpu_iova0 + offset;\n prp_list[k++] = next_4k_aligned_gpu_iova;\n ...\n cmd.prp1 = prp1; cmd.prp2 = prp_list_iova;\n `                                                      | PRP pages must be page-aligned; PRP2 can point to a PRP list (also page-aligned). ([nvmexpress.org][3])                                               |                                                    |                                                                                   |
| 5 | Append command to **I/O Submission Queue**                | userspace                       | ❌               | NVMe SQ layout + VFIO-mapped host buffer                      | `c\n sq[tail] = cmd; tail = (tail+1) % qdepth;\n mmio32(bar0 + DB_OFF_SQ(qid)) = tail; // doorbell\n `                                                                                                                                                    | Doorbell stride/calculation uses **CAP.DSTRD**; write doorbells via BAR0 MMIO you mmapped from VFIO. ([nvmexpress.org][4])                            |                                                    |                                                                                   |
| 6 | Poll **Completion Queue** and ack                         | userspace                       | ❌               | NVMe CQ layout                                                | `c\n while(!(cq[head].status & PHASE)) ;\n head=(head+1)%qdepth; mmio32(bar0 + DB_OFF_CQ(qid)) = head;\n `                                                                                                                                                | Keep **SQ/CQ in host RAM** so your userspace can read/write entries quickly. ([nvmexpress.org][4])                                                    |                                                    |                                                                                   |

---

### Why the split (GPU for data, **host RAM** for queues/PRP list)?

* **Queues need to be readable by your host code.** If you put SQ/CQ in GPU VRAM, your userspace cannot reasonably read them (CUDA device memory isn’t CPU-addressable), and many platforms won’t reliably support P2P fetch/store for all queue traffic. Keep **metadata** (SQ/CQ, PRP list pages) in **host RAM**, mapped with VFIO; point **data buffers** to GPU IOVAs. Linux’s P2PDMA docs also explain platform/topology pitfalls for P2P (same root complex/switch, ACS/ATS, etc.). ([리눅스 커널 문서][5])

---

## “Can the **Admin SQ/CQ** live in GPU memory?” (point ASQ/ACQ at GPU)

* **Practically: don’t.** The NVMe spec lets the host set **ASQ/ACQ** base addresses, but in real systems these are assumed to be normal system memory so host software can read/write queue entries. If you put ASQ/ACQ in GPU VRAM, your CPU code can’t poll CQ, and platform P2P constraints may drop you into undefined behavior. Create admin (and I/O) queues in **host RAM** and only route **data buffers** to GPU IOVA. ([OSDev 위키][6])

---

## Tiny code helpers you’ll reuse

**(A) VFIO map of host buffers (for SQ/CQ/PRP list)**

```c
// after VFIO container/group/device setup and TYPE1 IOMMU
void *prp_buf = aligned_alloc(4096, SZ);
struct vfio_iommu_type1_dma_map m = {
  .argsz=sizeof(m),
  .flags=VFIO_DMA_MAP_FLAG_READ|VFIO_DMA_MAP_FLAG_WRITE,
  .iova = 0x7000000000ULL,
  .vaddr=(uintptr_t)prp_buf, .size=SZ
};
ioctl(vfio_container, VFIO_IOMMU_MAP_DMA, &m);
uint64_t prp_list_iova = m.iova; // hand this to cmd.prp2
```

([리눅스 커널 문서][1])

**(B) Ask kernel shim for GPU→IOVA segments**

```c
gpu_p2p_map_req req = {.gpu_va=(uint64_t)dptr, .size=len,
                       .domain=0, .bus=0x5e, .devfn=(0x00<<3)|0};
ioctl(shim_fd, GPU_P2P_MAP, &req);
// req.segs[0..out_nsegs-1] => (iova,len) to feed PRPs
```

(Shim uses `nvidia_p2p_get_pages()` + `nvidia_p2p_dma_map_pages()` under the hood.) ([NVIDIA Docs][2])

**(C) Build PRPs that point into GPU**

```c
uint64_t prp1 = req.segs[0].iova + first_offset;
size_t   need = nlb * lba_size;
size_t   consumed = page_bytes - (prp1 & (page_bytes-1));
need -= consumed;
size_t prp_count = 0;
for (int s=0; s<req.out_nsegs && need; ++s) {
  uint64_t base=req.segs[s].iova, left=req.segs[s].len;
  if (s==0) { base += consumed; left -= consumed; }
  for (uint64_t p=0; p<left && need; p+=page_bytes) {
    ((uint64_t*)prp_buf)[prp_count++] = base + p;
    need -= need>page_bytes? page_bytes: need;
  }
}
cmd.prp1=prp1; cmd.prp2=prp_list_iova;  // and ring doorbell
```

(PRP alignment/continuation rules per NVMe Base Spec 2.0+) ([nvmexpress.org][3])

---

### Extra reminders

* **Topology matters** for P2P (keep GPU and NVMe under the same root complex/switch; beware ACS/ATS). ([리눅스 커널 문서][5])
* **Doorbells:** compute offsets with **CAP.DSTRD** (stride = 4 << DSTRD). ([nvmexpress.org][4])

If you want, I can drop in your actual BDF, queue sizes, and show the few missing VFIO device/bus setup calls to make a runnable “READ into VRAM” demo.

[1]: https://docs.kernel.org/driver-api/vfio.html?utm_source=chatgpt.com "VFIO - “Virtual Function I/O”"
[2]: https://docs.nvidia.com/cuda/pdf/GPUDirect_RDMA.pdf?utm_source=chatgpt.com "GPUDirect RDMA"
[3]: https://nvmexpress.org/wp-content/uploads/NVM-Express-Base-Specification-2.0d-2024.01.11-Ratified.pdf?utm_source=chatgpt.com "NVM Express Base Specification 2.0d"
[4]: https://www.nvmexpress.org/wp-content/uploads/NVM-Express-1_1a.pdf?utm_source=chatgpt.com "Non-Volatile Memory Host Controller Interface"
[5]: https://docs.kernel.org/driver-api/pci/p2pdma.html?utm_source=chatgpt.com "PCI Peer-to-Peer DMA Support"
[6]: https://wiki.osdev.org/NVMe?utm_source=chatgpt.com "NVMe"
