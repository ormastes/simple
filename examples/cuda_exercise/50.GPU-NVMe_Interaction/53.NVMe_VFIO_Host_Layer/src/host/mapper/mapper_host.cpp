/**
 * @file mapper_host.cpp
 * @brief Host-side implementation for NVMe memory mapper and device access
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

#include "mapper_host.h"
#include "memory/host_memory_buffer.h"
#include "io/io_impl.h"  // For CQE parsing functions

#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <linux/vfio.h>
#include <linux/fiemap.h>
#include <linux/fs.h>
#include <sys/stat.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cerrno>
#include <string>
#include <vector>
#include <algorithm>
#include <filesystem>

namespace {
constexpr size_t kPage = 4096;

// Import CQE parsing functions from io_impl.h
using nvme_io_impl::cqe_phase;
using nvme_io_impl::cqe_sct;
using nvme_io_impl::cqe_sc;

/// Round up size to alignment boundary
inline size_t round_up(size_t n, size_t a){ return (n + (a-1)) & ~(a-1); }

/// Allocate page-aligned and zero-initialized memory
/// @return Allocated pointer on success, nullptr on failure
inline void* page_alloc(size_t bytes){
  size_t rounded = round_up(bytes, kPage);
  void* p=nullptr;
  if (posix_memalign(&p, kPage, rounded)!=0){
    std::perror("posix_memalign");
    return nullptr;  // Return error instead of exit
  }
  std::memset(p, 0, rounded);
  return p;
}

/// Calculate NVMe doorbell stride from CAP register
inline uint32_t db_stride_bytes(uint64_t CAP){
  return 4u << ((uint32_t)((CAP >> 32) & 0xF));
}

/// RAII wrapper for FILE*
struct FCloser{ void operator()(FILE* f) const { if (f) std::fclose(f); } };
using FileUP = std::unique_ptr<FILE, FCloser>;

/// Helper: Check ioctl return and exit on error
/// @deprecated Use ioctl_check_noexit() for graceful error handling
/// @warning This function calls exit(1) on error - only for legacy admin commands
inline int ioctl_check(int fd, unsigned long request, void* arg, const char* name){
  int ret = ioctl(fd, request, arg);
  if (ret < 0 && name) {
    std::perror(name);
    std::exit(1);  // Legacy behavior - exit on admin command failures
  }
  return ret;
}

/// Helper: Check ioctl return and print error without exit (for graceful error handling)
inline int ioctl_check_noexit(int fd, unsigned long request, void* arg, const char* name){
  int ret = ioctl(fd, request, arg);
  if (ret < 0 && name) {
    std::perror(name);
  }
  return ret;
}

/// Helper: Check ioctl return and return error code on failure
inline int ioctl_safe(int fd, unsigned long request, void* arg){
  return ioctl(fd, request, arg);
}
} // namespace

struct NvmeDevice {
  int  container_fd{-1}, group_fd{-1}, device_fd{-1};
  int  bar_index{VFIO_PCI_BAR0_REGION_INDEX};
  void* bar0{nullptr}; size_t bar0_len{0};
  uint64_t next_iova{0x100000000ull};
  uint64_t CAP{0}; uint32_t VS{0};
  size_t page_size{4096};  // Dynamic page size (initialized from device capabilities)
  uint8_t mps_value{0};    // Memory Page Size value for CC.MPS field (0 = 4KB, 1 = 8KB, etc.)
  uint32_t lba_size{512};  // Logical block size in bytes (set during nvme_open, default 512B)
  ItemSize item_size{};         // Item size descriptor (configured during nvme_open)
  Queue asq{}, acq{}, iosq{}, iocq{};
  NvmeQueueStruct* queue_wrapper{nullptr};  // Tracks the queue wrapper for cleanup
  bool controller_enabled{false};  // Tracks controller enable state for page size validation

  volatile uint32_t* mmio32(uint32_t off) const { return reinterpret_cast<volatile uint32_t*>((uint8_t*)bar0 + off); }
  volatile uint64_t* mmio64(uint32_t off) const { return reinterpret_cast<volatile uint64_t*>((uint8_t*)bar0 + off); }

  /// Map host memory into device IOVA space for DMA
  /// @param host Host virtual address (must be page-aligned)
  /// @param sz Size in bytes (must be page-aligned)
  /// @return Device IOVA address for DMA operations, or 0 on failure
  uint64_t map_dma_aligned(void* host, size_t sz){
    // Check page alignment
    if (((uint64_t)host % page_size) != 0) {
      std::fprintf(stderr, "MAP_DMA: host address %p not page-aligned (requires %zu alignment)\n",
                   host, page_size);
      return 0;
    }
    if ((sz % page_size) != 0) {
      std::fprintf(stderr, "MAP_DMA: size %zu not page-aligned (requires %zu alignment)\n",
                   sz, page_size);
      return 0;
    }

    vfio_iommu_type1_dma_map m{};
    m.argsz = sizeof(m);
    m.vaddr = (uint64_t)host;
    m.size = sz;
    m.iova = next_iova;
    m.flags = VFIO_DMA_MAP_FLAG_READ | VFIO_DMA_MAP_FLAG_WRITE;

    if (ioctl(container_fd, VFIO_IOMMU_MAP_DMA, &m)!=0){
      std::fprintf(stderr, "MAP_DMA failed: vaddr=%p, size=%zu, iova=0x%lx, errno=%d (%s)\n",
                   (void*)m.vaddr, m.size, m.iova, errno, std::strerror(errno));
      return 0;  // Return 0 to indicate failure instead of exiting
    }

    next_iova += sz;
    return m.iova;
  }

  /// Unmap previously mapped DMA region
  /// @param iova Device IOVA address
  /// @param sz Size in bytes
  void unmap_dma(uint64_t iova, size_t sz){
    vfio_iommu_type1_dma_unmap u{};
    u.argsz = sizeof(u);
    u.iova = iova;
    u.size = sz;

    if (ioctl(container_fd, VFIO_IOMMU_UNMAP_DMA, &u)!=0){
      std::perror("UNMAP_DMA");
    }
  }

  void ring_sq_db(uint16_t qid, uint16_t tail){ *mmio32(nvme_reg::DOORBELL_BASE + db_stride_bytes(CAP)*(2u*qid)) = tail; }
  void ring_cq_db(uint16_t qid, uint16_t head){ *mmio32(nvme_reg::DOORBELL_BASE + db_stride_bytes(CAP)*(2u*qid+1u)) = head; }

  /// Open VFIO device and map BAR0 for NVMe register access
  bool open_vfio(const std::string& bdf){
    // Open VFIO container
    container_fd = ::open("/dev/vfio/vfio", O_RDWR);
    if (container_fd<0){ std::perror("open vfio"); return false; }

    // Check VFIO API version
    int api = ioctl_safe(container_fd, VFIO_GET_API_VERSION, nullptr);
    if (api != VFIO_API_VERSION){
      std::fprintf(stderr,"VFIO API mismatch (got %d, expected %d)\n", api, VFIO_API_VERSION);
      return false;
    }

    // Verify TYPE1 IOMMU support
    if (!ioctl_safe(container_fd, VFIO_CHECK_EXTENSION, (void*)(uintptr_t)VFIO_TYPE1_IOMMU)){
      std::fprintf(stderr,"VFIO TYPE1 IOMMU not supported\n");
      return false;
    }

    // Resolve IOMMU group for this device
    std::filesystem::path devp = std::string("/sys/bus/pci/devices/") + bdf + "/iommu_group";
    std::filesystem::path link;
    try {
      link = std::filesystem::read_symlink(devp);
    } catch (const std::exception& e) {
      std::fprintf(stderr, "Failed to read iommu_group symlink for %s: %s\n", bdf.c_str(), e.what());
      return false;
    }
    std::string group_path = "/dev/vfio/" + link.filename().string();

    // Open VFIO group and attach to container
    group_fd = ::open(group_path.c_str(), O_RDWR);
    if (group_fd<0){ std::perror("open group"); return false; }

    if (ioctl_check_noexit(group_fd, VFIO_GROUP_SET_CONTAINER, &container_fd, "SET_CONTAINER") < 0) return false;
    if (ioctl_check_noexit(container_fd, VFIO_SET_IOMMU, (void*)(uintptr_t)VFIO_TYPE1_IOMMU, "SET_IOMMU") < 0) return false;

    // Get device file descriptor
    device_fd = ioctl_safe(group_fd, VFIO_GROUP_GET_DEVICE_FD, (void*)bdf.c_str());
    if (device_fd<0){ std::perror("GET_DEVICE_FD"); return false; }

    // Map BAR0 (NVMe controller registers)
    vfio_region_info rinfo{ .argsz=sizeof(rinfo), .index=(uint32_t)bar_index };
    if (ioctl_check_noexit(device_fd, VFIO_DEVICE_GET_REGION_INFO, &rinfo, "REGION_INFO") < 0) return false;

    bar0_len = rinfo.size;
    bar0 = mmap(nullptr, bar0_len, PROT_READ|PROT_WRITE, MAP_SHARED, device_fd, rinfo.offset);
    if (bar0 == MAP_FAILED){ std::perror("mmap bar0"); return false; }

    // Read controller capabilities
    CAP = *mmio64(nvme_reg::CAP);
    VS = *mmio32(nvme_reg::VS);

    // Initialize page_size from CAP.MPSMIN and system page size
    // CAP.MPSMIN (bits 48:51) specifies minimum page size as 2^(12 + MPSMIN)
    uint8_t mpsmin = (uint8_t)((CAP >> 48) & 0xF);
    size_t nvme_min_page = 1UL << (12 + mpsmin);  // NVMe minimum page size
    size_t sys_page = (size_t)sysconf(_SC_PAGESIZE);  // System page size

    // Use the maximum of NVMe minimum, system page size, and 4KB
    page_size = std::max({nvme_min_page, sys_page, (size_t)4096});
    
    // Calculate corresponding MPS value for the selected page size
    mps_value = 0;
    size_t temp = page_size;
    while (temp > 4096) {
      temp >>= 1;
      mps_value++;
    }

    std::fprintf(stderr, "Page size: NVMe min=%zu, System=%zu, Using=%zu (MPS=%u)\n",
                 nvme_min_page, sys_page, page_size, mps_value);
    return true;
  }

  static inline uint32_t aqa(uint16_t asq_m1, uint16_t acq_m1){ return (uint32_t(asq_m1) | (uint32_t(acq_m1)<<16)); }
  static inline uint32_t cc(bool en, uint8_t mpsm12, uint8_t iosqes, uint8_t iocqes){
    return (uint32_t)en | (uint32_t(mpsm12)<<7) | (uint32_t(iosqes)<<16) | (uint32_t(iocqes)<<20);
  }

  bool controller_disable(){
    uint32_t v=*mmio32(nvme_reg::CC); v&=~1u; *mmio32(nvme_reg::CC)=v;
    for (int i=0;i<1000000;i++){ if (((*mmio32(nvme_reg::CSTS))&1u)==0) {
      controller_enabled = false;  // Mark controller as disabled
      return true;
    }}
    std::fprintf(stderr,"Timeout RDY=0\n");
    return false;
  }
  bool controller_enable(uint16_t qd){
    asq.entries=qd; asq.entry_size=64; acq.entries=qd; acq.entry_size=16;

    // Allocate admin submission queue
    size_t asz=round_up(asq.entries*asq.entry_size,page_size);
    asq.vaddr=page_alloc(asz);
    if (!asq.vaddr) {
      std::fprintf(stderr,"Failed to allocate admin submission queue (%zu bytes)\n", asz);
      return false;
    }
    asq.iova=map_dma_aligned(asq.vaddr,asz);

    // Allocate admin completion queue
    size_t csz=round_up(acq.entries*acq.entry_size,page_size);
    acq.vaddr=page_alloc(csz);
    if (!acq.vaddr) {
      std::fprintf(stderr,"Failed to allocate admin completion queue (%zu bytes)\n", csz);
      return false;
    }
    acq.iova=map_dma_aligned(acq.vaddr,csz);

    *mmio32(nvme_reg::AQA)=aqa(asq.entries-1,acq.entries-1);
    *mmio64(nvme_reg::ASQ)=asq.iova;
    *mmio64(nvme_reg::ACQ)=acq.iova;
    *mmio32(nvme_reg::CC)=cc(true,mps_value,6,4);

    for (int i=0;i<1000000;i++){ if (((*mmio32(nvme_reg::CSTS))&1u)==1u) break; }
    if (((*mmio32(nvme_reg::CSTS))&1u)!=1u){
      std::fprintf(stderr,"Timeout RDY=1\n");
      return false;
    }
    controller_enabled = true;  // Mark controller as enabled
    return true;
  }

  void admin_submit(const NvmeCmd& c){
    std::memcpy((uint8_t*)asq.vaddr + (size_t)asq.tail*asq.entry_size, &c, sizeof(c));
    asq.tail = (uint16_t)((asq.tail + 1) % asq.entries); ring_sq_db(0, asq.tail);
  }
  NvmeStatus admin_poll_complete(){
    for(;;){
      NvmeCqe* cq = (NvmeCqe*)((uint8_t*)acq.vaddr + (size_t)acq.head*acq.entry_size);
      if (cqe_phase(*cq)==acq.phase){
        uint8_t sct=cqe_sct(*cq), sc=cqe_sc(*cq);
        acq.head=(uint16_t)((acq.head+1)%acq.entries); if (acq.head==0) acq.phase^=1u; ring_cq_db(0, acq.head);
        return {sct, sc, false};
      }
      asm volatile("pause");
    }
  }
  bool create_iocq(uint16_t qid, uint16_t qd){
    iocq.entries=qd; iocq.entry_size=16; iocq.head=0; iocq.phase=1;

    // Allocate I/O completion queue
    size_t sz=round_up(iocq.entries*iocq.entry_size,page_size);
    iocq.vaddr=page_alloc(sz);
    if (!iocq.vaddr) {
      std::fprintf(stderr,"Failed to allocate I/O completion queue (%zu bytes)\n", sz);
      return false;
    }
    iocq.iova=map_dma_aligned(iocq.vaddr,sz);

    NvmeCmd c{}; c.opc=OPC_ADMIN_CREATE_IO_CQ; c.cid=1; c.nsid=0; c.prp1=iocq.iova;
    c.cdw10=((uint32_t)(qd-1)<<16)|qid; c.cdw11=(1u<<1) | 1u;
    admin_submit(c);
    NvmeStatus st = admin_poll_complete();
    if (st.is_error()){
      std::fprintf(stderr,"CREATE_IO_CQ failed (SCT=%u, SC=%u)\n", st.sct, st.sc);
      return false;
    }
    return true;
  }
  bool create_iosq(uint16_t qid, uint16_t qd, uint16_t cqid){
    iosq.entries=qd; iosq.entry_size=64; iosq.head=0; iosq.tail=0;

    // Allocate I/O submission queue
    size_t sz=round_up(iosq.entries*iosq.entry_size,page_size);
    iosq.vaddr=page_alloc(sz);
    if (!iosq.vaddr) {
      std::fprintf(stderr,"Failed to allocate I/O submission queue (%zu bytes)\n", sz);
      return false;
    }
    iosq.iova=map_dma_aligned(iosq.vaddr,sz);

    NvmeCmd c{}; c.opc=OPC_ADMIN_CREATE_IO_SQ; c.cid=2; c.nsid=0; c.prp1=iosq.iova;
    c.cdw10=((uint32_t)(qd-1)<<16)|qid; c.cdw11=((uint32_t)cqid<<16)|1u;
    admin_submit(c);
    NvmeStatus st = admin_poll_complete();
    if (st.is_error()){
      std::fprintf(stderr,"CREATE_IO_SQ failed (SCT=%u, SC=%u)\n", st.sct, st.sc);
      return false;
    }
    uint32_t stride=db_stride_bytes(CAP);
    iosq.qid=qid; iocq.qid=cqid;
    iosq.db=mmio32(nvme_reg::DOORBELL_BASE + stride*(2*qid+0));
    iocq.db=mmio32(nvme_reg::DOORBELL_BASE + stride*(2*cqid+1));

    // Note: Command pools will be initialized by nvme_setup_host_queue()
    // which is called separately after nvme_open()
    return true;
  }
  bool create_iocq_gpu(uint16_t qid, uint16_t qd, void* gpu_cq_dev_ptr, uint64_t gpu_cq_iova){
    if (!gpu_cq_dev_ptr || gpu_cq_iova == 0) {
      std::fprintf(stderr, "create_iocq_gpu: invalid GPU CQ pointer/IOVA\n");
      return false;
    }
    iocq.entries=qd; iocq.entry_size=16; iocq.head=0; iocq.phase=1;
    iocq.vaddr = gpu_cq_dev_ptr;  // CUDA device pointer (used only for aliasing)
    iocq.iova = gpu_cq_iova;      // Controller-visible DMA address

    NvmeCmd c{}; c.opc=OPC_ADMIN_CREATE_IO_CQ; c.cid=1; c.nsid=0; c.prp1=iocq.iova;
    c.cdw10=((uint32_t)(qd-1)<<16)|qid; c.cdw11=(1u<<1) | 1u;
    admin_submit(c);
    NvmeStatus st = admin_poll_complete();
    if (st.is_error()){
      std::fprintf(stderr,"CREATE_IO_CQ (GPU) failed (SCT=%u, SC=%u)\n", st.sct, st.sc);
      return false;
    }
    return true;
  }
};

// Global device pointer for mapping helpers (exported for host_memory_buffer.cpp)
NvmeDevice* g_dev = nullptr;

extern "C" {

/**
 * @brief Calculate best LBA size for given item size
 *
 * Selects the smallest LBA size from supported_lba_sizes that evenly divides item_size_bytes.
 * Using the smallest LBA size ensures compatibility with standard device formats (512B).
 *
 * @param item_size_bytes Desired transfer size in bytes
 * @param supported_lba_sizes Array of LBA sizes supported by device (e.g., {512, 4096})
 * @param num_supported Number of entries in supported_lba_sizes
 * @return Best LBA size, or 512 if none found
 */
static uint32_t calculate_best_lba_size(uint32_t item_size_bytes,
                                              const uint32_t* supported_lba_sizes,
                                              size_t num_supported) {
  uint32_t best_lba = 512;  // Default fallback (512B for universal compatibility)
  bool found = false;

  for (size_t i = 0; i < num_supported; i++) {
    uint32_t lba = supported_lba_sizes[i];
    // Check if this LBA size evenly divides the item size
    if (item_size_bytes % lba == 0) {
      // Pick the smallest one that divides evenly (for device compatibility)
      if (!found || lba < best_lba) {
        best_lba = lba;
        found = true;
      }
    }
  }

  return best_lba;
}

// New API: Initialize device without enabling controller (allows page size configuration)
NvmeDevice* nvme_init(const char* bdf, uint32_t item_size_bytes){
  auto* d=new NvmeDevice();

  // Supported LBA sizes (most NVMe devices support 512B and 4096B)
  // Future improvement: query supported LBA formats via Identify Namespace
  const uint32_t supported_lba_sizes[] = {512, 4096};
  const size_t num_supported = sizeof(supported_lba_sizes) / sizeof(supported_lba_sizes[0]);

  // Calculate best LBA size for requested item size
  uint32_t best_lba = calculate_best_lba_size(item_size_bytes, supported_lba_sizes, num_supported);
  d->lba_size = best_lba;

  // Calculate ItemSize
  d->item_size.total_size = item_size_bytes;
  d->item_size.lba_size = best_lba;
  d->item_size.lba_count = item_size_bytes / best_lba;

  std::printf("nvme_init: item_size=%u bytes, selected LBA size=%u, LBA count=%u\n",
              item_size_bytes, best_lba, d->item_size.lba_count);

  // Initialize device with error checking
  if (!d->open_vfio(bdf)) {
    std::fprintf(stderr, "nvme_init: Failed to open VFIO for device %s\n", bdf);
    delete d;
    return nullptr;
  }

  if (!d->controller_disable()) {
    std::fprintf(stderr, "nvme_init: Failed to disable controller for device %s\n", bdf);
    nvme_close(d);
    return nullptr;
  }

  // Device is now ready for page size configuration
  std::printf("nvme_init: Device %s initialized, controller disabled. Ready for configuration.\n", bdf);
  return d;
}

// New API: Enable controller with configured settings
bool nvme_enable(NvmeDevice* d, uint16_t admin_qd, uint16_t io_qd) {
  if (!d) {
    std::fprintf(stderr, "nvme_enable: null device\n");
    return false;
  }

  if (d->controller_enabled) {
    std::fprintf(stderr, "nvme_enable: controller already enabled\n");
    return false;
  }

  if (!d->controller_enable(admin_qd)) {
    std::fprintf(stderr, "nvme_enable: Failed to enable controller\n");
    return false;
  }

  if (!d->create_iocq(1,io_qd)) {
    std::fprintf(stderr, "nvme_enable: Failed to create I/O completion queue\n");
    return false;
  }

  if (!d->create_iosq(1,io_qd,1)) {
    std::fprintf(stderr, "nvme_enable: Failed to create I/O submission queue\n");
    return false;
  }

  g_dev = d;  // Store global device for mapping helpers
  std::printf("nvme_enable: Controller enabled, I/O queues created\n");
  return true;
}

int nvme_create_gpu_cq(NvmeDevice* dev,
                       uint16_t cqid,
                       void* gpu_cq_dev_ptr,
                       uint64_t gpu_cq_iova,
                       uint16_t gpu_cq_entries) {
  if (!dev) return -1;
  // Controller must already be enabled; this is an advanced path.
  if (!dev->controller_enabled) {
    std::fprintf(stderr, "nvme_create_gpu_cq: controller not enabled\n");
    return -2;
  }
  if (!dev->create_iocq_gpu(cqid, gpu_cq_entries, gpu_cq_dev_ptr, gpu_cq_iova)) {
    return -3;
  }
  return 0;
}

int nvme_create_host_sq_for_cq(NvmeDevice* dev,
                               uint16_t sq_entries,
                               uint16_t cqid) {
  if (!dev) return -1;
  if (!dev->controller_enabled) {
    std::fprintf(stderr, "nvme_create_host_sq_for_cq: controller not enabled\n");
    return -2;
  }
  if (!dev->create_iosq(1 /*qid*/, sq_entries, cqid)) {
    return -3;
  }
  return 0;
}

// Legacy API: Maintain backward compatibility
NvmeDevice* nvme_open(const char* bdf, uint16_t admin_qd, uint16_t io_qd, uint32_t item_size_bytes){
  // Use new API internally
  NvmeDevice* d = nvme_init(bdf, item_size_bytes);
  if (!d) return nullptr;

  // Enable controller with default settings
  if (!nvme_enable(d, admin_qd, io_qd)) {
    nvme_close(d);
    return nullptr;
  }

  return d;
}

void nvme_close(NvmeDevice* d){
  if (!d) return;

  // Clean up queue wrapper if it exists
  // This handles command pool cleanup automatically
  if (d->queue_wrapper) {
    nvme_cleanup_host_queue(d->queue_wrapper);
    d->queue_wrapper = nullptr;
  }

  // Disable controller
  d->controller_disable();

  // Unmap BAR0
  if (d->bar0 && d->bar0_len > 0) {
    munmap(d->bar0, d->bar0_len);
  }

  // Close file descriptors
  if (d->device_fd >= 0) close(d->device_fd);
  if (d->group_fd >= 0) close(d->group_fd);
  if (d->container_fd >= 0) close(d->container_fd);

  // Clear global device if this was it
  if (g_dev == d) g_dev = nullptr;

  delete d;
}

Queue* nvme_get_iosq(NvmeDevice* d){
    DEBUG_ASSERT(d != nullptr, "nvme_get_iosq: device is null");
    return &d->iosq;
}

Queue* nvme_get_iocq(NvmeDevice* d){
    DEBUG_ASSERT(d != nullptr, "nvme_get_iocq: device is null");
    return &d->iocq;
}

size_t nvme_get_page_size(NvmeDevice* d){
  return d ? d->page_size : 4096;
}

size_t nvme_get_max_page_size(NvmeDevice* d){
  if (!d) return 4096;

  // NVMe CAP.MPSMAX (bits 52:55) specifies maximum page size as 2^(12 + MPSMAX)
  uint8_t mpsmax = (uint8_t)((d->CAP >> 52) & 0xF);
  size_t nvme_max_page = 1UL << (12 + mpsmax);  // NVMe maximum page size

  return nvme_max_page;
}

bool nvme_set_page_size(NvmeDevice* d, size_t page_size){
  if (!d) {
    std::fprintf(stderr, "nvme_set_page_size: null device\n");
    return false;
  }
  
  // CRITICAL: Page size can only be changed when controller is disabled
  // According to NVMe spec, CC.MPS cannot be modified while CC.EN=1
  if (d->controller_enabled) {
    std::fprintf(stderr, "nvme_set_page_size: cannot change page size while controller is enabled.\n");
    std::fprintf(stderr, "  Call nvme_set_page_size() before nvme_open() completes controller initialization.\n");
    return false;
  }
  
  // Validate page size is power of 2 and >= 4KB
  if (page_size < 4096 || (page_size & (page_size - 1)) != 0) {
    std::fprintf(stderr, "nvme_set_page_size: invalid page size %zu (must be power of 2, >= 4KB)\n", page_size);
    return false;
  }
  
  // Calculate MPS value: log2(page_size) - 12
  uint8_t mps = 0;
  size_t temp = page_size;
  while (temp > 4096) {
    temp >>= 1;
    mps++;
  }
  
  // Validate against CAP.MPSMIN and CAP.MPSMAX
  uint8_t mpsmin = (uint8_t)((d->CAP >> 48) & 0xF);
  uint8_t mpsmax = (uint8_t)((d->CAP >> 52) & 0xF);
  
  if (mps < mpsmin) {
    std::fprintf(stderr, "nvme_set_page_size: page size %zu too small (min: %zu)\n", 
                 page_size, 1UL << (12 + mpsmin));
    return false;
  }
  
  if (mps > mpsmax) {
    std::fprintf(stderr, "nvme_set_page_size: page size %zu too large (max: %zu)\n", 
                 page_size, 1UL << (12 + mpsmax));
    return false;
  }
  
  // Store the page size and MPS value for later use in controller_enable()
  d->page_size = page_size;
  d->mps_value = mps;  // This would need to be added to NvmeDevice struct
  
  std::fprintf(stderr, "nvme_set_page_size: configured page size %zu bytes (MPS=%u)\n", page_size, mps);
  return true;
}

size_t* nvme_available_sizes(NvmeDevice* d, size_t* array_size){
  if (!d || !array_size) {
    if (array_size) *array_size = 0;
    return nullptr;
  }
  
  // Get MPSMIN and MPSMAX from CAP register
  uint8_t mpsmin = (uint8_t)((d->CAP >> 48) & 0xF);
  uint8_t mpsmax = (uint8_t)((d->CAP >> 52) & 0xF);
  
  // Calculate number of supported sizes
  size_t count = (mpsmax - mpsmin) + 1;
  *array_size = count;
  
  // Allocate array
  size_t* sizes = (size_t*)malloc(count * sizeof(size_t));
  if (!sizes) {
    *array_size = 0;
    return nullptr;
  }
  
  // Fill array with supported page sizes
  for (size_t i = 0; i < count; i++) {
    sizes[i] = 1UL << (12 + mpsmin + i);
  }
  
  return sizes;
}

uint32_t nvme_get_lba_size(NvmeDevice* d){
  return d ? d->lba_size : 512;
}

ItemSize nvme_get_item_size(NvmeDevice* d){
  if (!d) {
    // Return default ItemSize for null device (512B LBA)
    return ItemSize{512, 512, 1};
  }
  return d->item_size;
}

DoorbellMode nvme_get_support_doorbell(NvmeDevice* d){
  if (!d) return DOORBELL_MODE_HOST_MMIO;

  // Check NVMe CAP register for doorbell buffer config (DBC) support
  // CAP.DSTRD (bits 32:35) - Doorbell Stride (always supported)
  // For advanced doorbell modes, we need to check optional features

  // All NVMe devices support MMIO doorbell (basic mode)
  // Host DBC modes are software optimizations that don't require
  // specific hardware support beyond basic doorbell mechanism

  // For now, return DOORBELL_MODE_HOST_DBC as the most advanced supported mode
  // This indicates the device supports all host doorbell modes:
  // - DOORBELL_MODE_HOST_MMIO (always supported)
  // - DOORBELL_MODE_HOST_DBC_DAEMON (software optimization)
  // - DOORBELL_MODE_HOST_DBC (hardware DBC if supported)

  // Note: In a real implementation, you might want to check:
  // 1. Shadow doorbell buffer support (NVMe 1.3+) via DBBUF admin command
  // 2. Controller configuration for specific optimizations
  // 3. Driver capabilities and preferences

  return DOORBELL_MODE_HOST_DBC;  // Highest capability (includes all modes)
}

int nvme_get_device_fd(NvmeDevice* d){
  if (!d) return -1;
  return d->device_fd;
}

// ---------- Mapping helpers ----------
int host_map_iova(void* host, size_t bytes, uint64_t* out_iova){
  if (!g_dev || !host || !bytes || !out_iova) return -1;

  // Ensure page alignment
  const size_t page_size = g_dev->page_size;
  size_t aligned_bytes = round_up(bytes, page_size);
  if (aligned_bytes != bytes) {
    std::fprintf(stderr, "host_map_iova: rounding size %zu up to %zu for page alignment (%zu)\n",
                 bytes, aligned_bytes, page_size);
  }

  uint64_t iova = g_dev->map_dma_aligned(host, aligned_bytes);
  if (iova == 0) {
    return -1;  // map_dma_aligned already printed error
  }

  *out_iova = iova;
  return 0;
}

int host_unmap_iova(void* host, size_t bytes, uint64_t iova){
  if (!g_dev || !host || !bytes || !iova) return -1;
  g_dev->unmap_dma(iova, bytes);
  return 0;
}

// ============================================================================
// Host Queue Setup
// ============================================================================

int nvme_setup_host_queue(
    NvmeDevice* nvme_dev,
    const char* nvme_bdf,
    NvmeQueueStruct* out_queue
)
{
    if (!nvme_dev || !out_queue) {
        std::fprintf(stderr, "nvme_setup_host_queue: Invalid arguments\n");
        return -1;
    }

    // Get IO queues from NVMe device
    Queue* iosq = nvme_get_iosq(nvme_dev);
    Queue* iocq = nvme_get_iocq(nvme_dev);

    if (!iosq || !iocq || !iosq->vaddr || !iocq->vaddr) {
        std::fprintf(stderr, "nvme_setup_host_queue: Invalid IO queues\n");
        return -1;
    }

    // Zero out the structure
    std::memset(out_queue, 0, sizeof(NvmeQueueStruct));

    // Populate queue descriptor from existing Queue structures
    out_queue->sq_base = static_cast<NvmeCmd*>(iosq->vaddr);
    out_queue->cq_base = static_cast<NvmeCqe*>(iocq->vaddr);
    out_queue->sq_addr = iosq->vaddr;
    out_queue->cq_addr = iocq->vaddr;
    // Note: doorbell pointers are not stored in NvmeQueueStruct directly
    // They should be managed through the doorbell strategy objects
    out_queue->sq_depth = iosq->entries;
    out_queue->cq_depth = iocq->entries;
    out_queue->qid = iosq->qid;
    out_queue->sq_phase = 1;  // Initial phase
    out_queue->cq_phase = iocq->phase;
    out_queue->doorbell_mode = DOORBELL_MODE_HOST_MMIO;  // Host-managed doorbell
    out_queue->sq_tail = iosq->tail;
    out_queue->cq_head = iocq->head;

    // Get ItemSize, page size, and nsid from device
    out_queue->item_size = nvme_get_item_size(nvme_dev);
    out_queue->page_size = static_cast<uint32_t>(nvme_get_page_size(nvme_dev));
    out_queue->nsid = 1;  // Default namespace ID (standard for NVMe)

    // Allocate and pre-build READ command pool
    out_queue->read_cmd_pool = new NvmeCmd[iosq->entries];
    std::memset(out_queue->read_cmd_pool, 0, sizeof(NvmeCmd) * iosq->entries);

    // Allocate and pre-build WRITE command pool
    out_queue->write_cmd_pool = new NvmeCmd[iosq->entries];
    std::memset(out_queue->write_cmd_pool, 0, sizeof(NvmeCmd) * iosq->entries);

    // Also populate the command pools in the underlying Queue structure
    iosq->read_cmd_pool = out_queue->read_cmd_pool;
    iosq->write_cmd_pool = out_queue->write_cmd_pool;

    // Pre-build all commands in the pools
    // Commands will be copied to SQ and have their CID/SLBA/PRP updated at submission time
    const uint16_t nlb = out_queue->item_size.nlb();
    const uint32_t nsid = out_queue->nsid;

    for (uint16_t cid = 0; cid < iosq->entries; cid++) {
        // Pre-build READ command template
        NvmeCmd& read_cmd = out_queue->read_cmd_pool[cid];
        read_cmd.opc = OPC_NVM_READ;
        read_cmd.cid = cid;
        read_cmd.nsid = nsid;
        read_cmd.cdw12 = static_cast<uint32_t>(nlb);
        // Note: prp1, prp2, slba will be filled at submission time from DmaBuf

        // Pre-build WRITE command template
        NvmeCmd& write_cmd = out_queue->write_cmd_pool[cid];
        write_cmd.opc = OPC_NVM_WRITE;
        write_cmd.cid = cid;
        write_cmd.nsid = nsid;
        write_cmd.cdw12 = static_cast<uint32_t>(nlb);
        // Note: prp1, prp2, slba will be filled at submission time from DmaBuf
    }

    std::fprintf(stderr, "INFO: nvme_setup_host_queue() - Pre-built %u READ and %u WRITE commands (LBA size=%u, count=%u)\n",
                 iosq->entries, iosq->entries, out_queue->item_size.lba_size, out_queue->item_size.lba_count);

    // Track the queue wrapper in the device for automatic cleanup
    nvme_dev->queue_wrapper = out_queue;

    return 0;
}

void nvme_cleanup_host_queue(NvmeQueueStruct* queue) {
    if (!queue) return;

    // Clean up command pools and null out shared references in device's internal iosq
    // to prevent double-free in nvme_close()
    if (queue->read_cmd_pool) {
        NvmeCmd* read_pool_ptr = queue->read_cmd_pool;
        delete[] queue->read_cmd_pool;
        queue->read_cmd_pool = nullptr;

        // Null out the shared reference in global device if it points to same memory
        if (g_dev && g_dev->iosq.read_cmd_pool == read_pool_ptr) {
            g_dev->iosq.read_cmd_pool = nullptr;
        }
    }

    if (queue->write_cmd_pool) {
        NvmeCmd* write_pool_ptr = queue->write_cmd_pool;
        delete[] queue->write_cmd_pool;
        queue->write_cmd_pool = nullptr;

        // Null out the shared reference in global device if it points to same memory
        if (g_dev && g_dev->iosq.write_cmd_pool == write_pool_ptr) {
            g_dev->iosq.write_cmd_pool = nullptr;
        }
    }
}

} // extern "C"
