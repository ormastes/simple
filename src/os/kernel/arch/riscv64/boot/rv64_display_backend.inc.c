/* RISC-V64 VirtIO-GPU display backend (shared boot fragment).
 *
 * Extracted verbatim from freestanding_runtime.c so that BOTH riscv64 boot
 * directories can link the same implementation. native-build derives its boot
 * directory as `<entry>.parent()/boot`, so every lane whose entry lives under
 * examples/09_embedded/simple_os/arch/riscv64/ linked a boot set with NO PCI or
 * VirtIO-GPU code at all, while this real driver sat in the src/ boot dir that
 * only src/os/kernel/arch/riscv64/user_entry.spl reaches. That is why the WM
 * render-smoke kernel failed to link on rt_display_*.
 *
 * Included (never compiled standalone: the name ends in .inc.c but the boot
 * autodiscovery compiles every *.c stem, so this file must only ever be
 * reached through a #include from a real TU).
 * Keep it libc-free: no includes, no malloc, no formatted I/O.
 */
typedef struct RtPciDevice {
    spl_i64 bus;
    spl_i64 device;
    spl_i64 function;
    spl_i64 class_code;
    spl_i64 subclass;
    spl_i64 vendor;
    spl_i64 device_id;
    spl_i64 bar0;
    spl_i64 irq;
} RtPciDevice;

#define RT_PCI_ECAM_BASE 0x30000000ULL
#define RT_PCI_IO_BASE 0x03000000ULL
#define RT_PCI_MMIO_BASE 0x40000000ULL
#define RT_PCI_LEGACY_NET_IO_PORT 0x1000ULL
#define RT_PCI_LEGACY_GPU_IO_PORT 0x2000ULL
#define RT_PCI_LEGACY_BLK_IO_PORT 0x3000ULL
#define RT_PCI_CMD_IO 0x1U
#define RT_PCI_CMD_MEM 0x2U
#define RT_PCI_CMD_BUS_MASTER 0x4U
#define RT_PCI_MAX_DEVICES 32
#define RT_VIRTIO_VENDOR_ID 0x1af4
#define RT_VIRTIO_NET_LEGACY_DEVICE_ID 0x1000
#define RT_VIRTIO_NET_MODERN_DEVICE_ID 0x1041
#define RT_VIRTIO_BLK_LEGACY_DEVICE_ID 0x1001
#define RT_VIRTIO_BLK_MODERN_DEVICE_ID 0x1042
#define RT_VIRTIO_GPU_LEGACY_DEVICE_ID 0x1010
#define RT_VIRTIO_GPU_MODERN_DEVICE_ID 0x1050
#define RT_VIRTIO_PCI_HOST_FEATURES 0x00ULL
#define RT_VIRTIO_PCI_GUEST_FEATURES 0x04ULL
#define RT_VIRTIO_PCI_QUEUE_PFN 0x08ULL
#define RT_VIRTIO_PCI_QUEUE_SIZE 0x0cULL
#define RT_VIRTIO_PCI_QUEUE_SEL 0x0eULL
#define RT_VIRTIO_PCI_QUEUE_NOTIFY 0x10ULL
#define RT_VIRTIO_PCI_STATUS 0x12ULL
#define RT_VIRTIO_NET_MAC_OFFSET 0x14ULL
#define RT_PCI_CAP_ID_VENDOR_SPECIFIC 0x09U
#define RT_VIRTIO_PCI_CAP_COMMON_CFG 1U
#define RT_VIRTIO_PCI_CAP_NOTIFY_CFG 2U
#define RT_VIRTIO_MODERN_DEVICE_FEATURE_SELECT 0x00ULL
#define RT_VIRTIO_MODERN_DEVICE_FEATURE 0x04ULL
#define RT_VIRTIO_MODERN_DRIVER_FEATURE_SELECT 0x08ULL
#define RT_VIRTIO_MODERN_DRIVER_FEATURE 0x0cULL
#define RT_VIRTIO_MODERN_NUM_QUEUES 0x12ULL
#define RT_VIRTIO_MODERN_DEVICE_STATUS 0x14ULL
#define RT_VIRTIO_MODERN_QUEUE_SELECT 0x16ULL
#define RT_VIRTIO_MODERN_QUEUE_SIZE 0x18ULL
#define RT_VIRTIO_MODERN_QUEUE_ENABLE 0x1cULL
#define RT_VIRTIO_MODERN_QUEUE_NOTIFY_OFF 0x1eULL
#define RT_VIRTIO_MODERN_QUEUE_DESC_LO 0x20ULL
#define RT_VIRTIO_MODERN_QUEUE_DESC_HI 0x24ULL
#define RT_VIRTIO_MODERN_QUEUE_DRIVER_LO 0x28ULL
#define RT_VIRTIO_MODERN_QUEUE_DRIVER_HI 0x2cULL
#define RT_VIRTIO_MODERN_QUEUE_DEVICE_LO 0x30ULL
#define RT_VIRTIO_MODERN_QUEUE_DEVICE_HI 0x34ULL
#define RT_VIRTIO_STATUS_ACKNOWLEDGE 1U
#define RT_VIRTIO_STATUS_DRIVER 2U
#define RT_VIRTIO_STATUS_DRIVER_OK 4U
#define RT_VIRTIO_STATUS_FEATURES_OK 8U
#define RT_VIRTIO_STATUS_FAILED 128U
#define RT_VIRTIO_NET_RX_QUEUE 0U
#define RT_VIRTIO_NET_TX_QUEUE 1U
#define RT_VIRTIO_NET_HDR_SIZE 10U
#define RT_VIRTIO_NET_F_MAC (1U << 5)
#define RT_VIRTQ_DESC_F_NEXT 1U
#define RT_VIRTQ_DESC_F_WRITE 2U
#define RT_NET_QUEUE_CAP 256U
#define RT_NET_RX_POST_COUNT 8U
#define RT_NET_BUFFER_SIZE 2048U
#define RT_VIRTIO_BLK_QUEUE 0U
#define VIRTIO_BLK_T_IN 0U
#define VIRTIO_BLK_T_OUT 1U
#define RT_VIRTIO_BLK_CONFIG_CAPACITY 0x14ULL
#define RT_VIRTIO_BLK_SECTOR_SIZE 512U
#define RT_NVFS_MAGIC 0x4e564653U
#define RT_NVFS_VERSION 2U
#define RT_GPU_QUEUE_CAP 64U
#define RT_GPU_WIDTH 320U
#define RT_GPU_HEIGHT 240U
#define RT_GPU_RESOURCE_ID 1U
#define RT_GPU_CMD_GET_DISPLAY_INFO 0x0100U
#define RT_GPU_CMD_RESOURCE_CREATE_2D 0x0101U
#define RT_GPU_CMD_SET_SCANOUT 0x0103U
#define RT_GPU_CMD_RESOURCE_FLUSH 0x0104U
#define RT_GPU_CMD_TRANSFER_TO_HOST_2D 0x0105U
#define RT_GPU_CMD_RESOURCE_ATTACH_BACKING 0x0106U
#define RT_GPU_RESP_OK_NODATA 0x1100U
#define RT_GPU_RESP_OK_DISPLAY_INFO 0x1101U
#define RT_GPU_FORMAT_B8G8R8A8_UNORM 1U

static RtPciDevice g_rt_pci_devices[RT_PCI_MAX_DEVICES];
static spl_i64 g_rt_pci_count = -1;
static spl_i64 g_rt_net_ready = 0;
static spl_i64 g_rt_net_tx_ready = 0;
static spl_i64 g_rt_net_rx_ready = 0;
static spl_i64 g_rt_net_tx_probe_code = -1;
static spl_u64 g_rt_net_bar0 = 0;
static spl_u64 g_rt_rx_desc = 0;
static spl_u64 g_rt_rx_avail = 0;
static spl_u64 g_rt_rx_used = 0;
static spl_u64 g_rt_rx_bufs = 0;
static spl_u16 g_rt_rx_qsize = 0;
static spl_u16 g_rt_rx_last_used = 0;
static spl_u64 g_rt_tx_desc = 0;
static spl_u64 g_rt_tx_avail = 0;
static spl_u64 g_rt_tx_used = 0;
static spl_u64 g_rt_tx_bufs = 0;
static spl_u16 g_rt_tx_qsize = 0;
static spl_u16 g_rt_tx_last_used = 0;
static spl_i64 g_rt_storage_ready = 0;
static spl_i64 g_rt_storage_probe_ready = 0;
static spl_u64 g_rt_blk_bar0 = 0;
static spl_u64 g_rt_blk_desc = 0;
static spl_u64 g_rt_blk_avail = 0;
static spl_u64 g_rt_blk_used = 0;
static spl_u16 g_rt_blk_qsize = 0;
static spl_u16 g_rt_blk_last_used = 0;
static spl_u64 g_rt_blk_req = 0;
static spl_u64 g_rt_blk_data = 0;
static spl_u64 g_rt_blk_capacity = 0;
static spl_i64 g_rt_blk_nvfs_ready = 0;
static spl_i64 g_rt_blk_nvfs_arena_ready = 0;
static spl_i64 g_rt_display_ready = 0;
static spl_i64 g_rt_gpu_modern = 0;
static spl_u64 g_rt_gpu_bar0 = 0;
static spl_u64 g_rt_gpu_common = 0;
static spl_u64 g_rt_gpu_notify = 0;
static spl_u32 g_rt_gpu_notify_multiplier = 0;
static spl_u16 g_rt_gpu_notify_off = 0;
static spl_u64 g_rt_gpu_desc = 0;
static spl_u64 g_rt_gpu_avail = 0;
static spl_u64 g_rt_gpu_used = 0;
static spl_u16 g_rt_gpu_qsize = 0;
static spl_u16 g_rt_gpu_last_used = 0;
static spl_u64 g_rt_gpu_cmd = 0;
static spl_u64 g_rt_gpu_resp = 0;
static spl_u64 g_rt_gpu_fb = 0;

static spl_u32 rt_pci_read_config32(spl_u64 bus, spl_u64 dev, spl_u64 func, spl_u64 reg) {
    spl_u64 addr = RT_PCI_ECAM_BASE
        + (bus << 20)
        + (dev << 15)
        + (func << 12)
        + (reg & ~3ULL);
    return *(volatile spl_u32 *)addr;
}

static spl_u8 rt_pci_read_config8(spl_u64 bus, spl_u64 dev, spl_u64 func, spl_u64 reg) {
    spl_u64 addr = RT_PCI_ECAM_BASE
        + (bus << 20)
        + (dev << 15)
        + (func << 12)
        + reg;
    return *(volatile spl_u8 *)addr;
}

static void rt_pci_write_config32(spl_u64 bus, spl_u64 dev, spl_u64 func, spl_u64 reg, spl_u32 value) {
    spl_u64 addr = RT_PCI_ECAM_BASE
        + (bus << 20)
        + (dev << 15)
        + (func << 12)
        + (reg & ~3ULL);
    *(volatile spl_u32 *)addr = value;
}

static spl_u8 rt_mmio_read8_raw(spl_u64 addr) {
    return *(volatile spl_u8 *)addr;
}

static spl_u16 rt_mmio_read16_raw(spl_u64 addr) {
    return *(volatile spl_u16 *)addr;
}

static void rt_mmio_write8_raw(spl_u64 addr, spl_u8 value) {
    *(volatile spl_u8 *)addr = value;
}

static void rt_mmio_write16_raw(spl_u64 addr, spl_u16 value) {
    *(volatile spl_u16 *)addr = value;
}

static void rt_mmio_write32_raw(spl_u64 addr, spl_u32 value) {
    *(volatile spl_u32 *)addr = value;
}

static spl_u8 rt_io_read8(spl_u64 base, spl_u64 off) {
    return *(volatile spl_u8 *)(base + off);
}

static spl_u16 rt_io_read16(spl_u64 base, spl_u64 off) {
    return *(volatile spl_u16 *)(base + off);
}

static spl_u32 rt_io_read32(spl_u64 base, spl_u64 off) {
    return *(volatile spl_u32 *)(base + off);
}

static void rt_io_write8(spl_u64 base, spl_u64 off, spl_u8 value) {
    *(volatile spl_u8 *)(base + off) = value;
}

static void rt_io_write16(spl_u64 base, spl_u64 off, spl_u16 value) {
    *(volatile spl_u16 *)(base + off) = value;
}

static void rt_io_write32(spl_u64 base, spl_u64 off, spl_u32 value) {
    *(volatile spl_u32 *)(base + off) = value;
}

static void rt_memzero(void *ptr, spl_u64 bytes) {
    spl_u8 *data = (spl_u8 *)ptr;
    for (spl_u64 i = 0; i < bytes; i = i + 1) {
        data[i] = 0;
    }
}

static spl_u64 rt_alloc_contiguous_pages(spl_u64 pages) {
    spl_u64 base = 0;
    spl_u64 prev = 0;
    if (pages == 0) {
        return 0;
    }
    for (spl_u64 i = 0; i < pages; i = i + 1) {
        spl_u64 page = spl_riscv_noalloc_alloc_page();
        if (page == 0) {
            return 0;
        }
        if (i == 0) {
            base = page;
        } else if (page != prev + 4096ULL) {
            return 0;
        }
        prev = page;
    }
    return base;
}

static spl_u64 rt_virtqueue_desc_size(spl_u16 qsize) {
    return (spl_u64)qsize * 16ULL;
}

static spl_u64 rt_virtqueue_avail_size(spl_u16 qsize) {
    return 4ULL + 2ULL * (spl_u64)qsize;
}

static spl_u64 rt_virtqueue_total_size(spl_u16 qsize) {
    spl_u64 desc_avail = rt_virtqueue_desc_size(qsize) + rt_virtqueue_avail_size(qsize);
    spl_u64 used = 4ULL + 8ULL * (spl_u64)qsize;
    return ((desc_avail + 4095ULL) & ~4095ULL) + used;
}

static void rt_desc_write(spl_u64 desc_base, spl_u16 idx, spl_u64 addr, spl_u32 len, spl_u16 flags, spl_u16 next) {
    volatile spl_u32 *lo = (volatile spl_u32 *)(desc_base + (spl_u64)idx * 16ULL);
    volatile spl_u32 *hi = (volatile spl_u32 *)(desc_base + (spl_u64)idx * 16ULL + 4ULL);
    volatile spl_u32 *dlen = (volatile spl_u32 *)(desc_base + (spl_u64)idx * 16ULL + 8ULL);
    volatile spl_u16 *dflags = (volatile spl_u16 *)(desc_base + (spl_u64)idx * 16ULL + 12ULL);
    volatile spl_u16 *dnext = (volatile spl_u16 *)(desc_base + (spl_u64)idx * 16ULL + 14ULL);
    *lo = (spl_u32)(addr & 0xffffffffULL);
    *hi = (spl_u32)(addr >> 32);
    *dlen = len;
    *dflags = flags;
    *dnext = next;
}

static void rt_avail_push(spl_u64 avail_base, spl_u16 qsize, spl_u16 desc_idx) {
    volatile spl_u16 *idxp = (volatile spl_u16 *)(avail_base + 2ULL);
    spl_u16 idx = *idxp;
    volatile spl_u16 *slot = (volatile spl_u16 *)(avail_base + 4ULL + ((spl_u64)(idx % qsize) * 2ULL));
    *slot = desc_idx;
    *idxp = idx + 1U;
}

static spl_i64 rt_setup_virtqueue(spl_u64 bar0, spl_u16 queue, spl_u64 *desc, spl_u64 *avail, spl_u64 *used, spl_u16 *qsize) {
    spl_u16 max_size;
    spl_u16 size;
    spl_u64 total;
    spl_u64 ring;
    spl_u64 pages;
    spl_u64 desc_avail;
    rt_io_write16(bar0, RT_VIRTIO_PCI_QUEUE_SEL, queue);
    max_size = rt_io_read16(bar0, RT_VIRTIO_PCI_QUEUE_SIZE);
    if (max_size == 0) {
        return -1;
    }
    if (max_size > RT_NET_QUEUE_CAP) {
        return -1;
    }
    size = max_size;
    total = rt_virtqueue_total_size(size);
    pages = (total + 4095ULL) / 4096ULL;
    ring = rt_alloc_contiguous_pages(pages);
    if (ring == 0) {
        return -1;
    }
    rt_memzero((void *)ring, pages * 4096ULL);
    desc_avail = rt_virtqueue_desc_size(size) + rt_virtqueue_avail_size(size);
    *desc = ring;
    *avail = ring + rt_virtqueue_desc_size(size);
    *used = ring + ((desc_avail + 4095ULL) & ~4095ULL);
    *qsize = size;
    rt_io_write32(bar0, RT_VIRTIO_PCI_QUEUE_PFN, (spl_u32)(ring >> 12));
    return 0;
}

static spl_i64 rt_setup_virtqueue_capped(spl_u64 bar0, spl_u16 queue, spl_u16 cap, spl_u64 *desc, spl_u64 *avail, spl_u64 *used, spl_u16 *qsize) {
    spl_u16 max_size;
    spl_u16 size;
    spl_u64 total;
    spl_u64 ring;
    spl_u64 pages;
    spl_u64 desc_avail;
    rt_io_write16(bar0, RT_VIRTIO_PCI_QUEUE_SEL, queue);
    max_size = rt_io_read16(bar0, RT_VIRTIO_PCI_QUEUE_SIZE);
    if (max_size == 0) {
        return -1;
    }
    size = max_size > cap ? cap : max_size;
    total = rt_virtqueue_total_size(size);
    pages = (total + 4095ULL) / 4096ULL;
    ring = rt_alloc_contiguous_pages(pages);
    if (ring == 0) {
        return -1;
    }
    rt_memzero((void *)ring, pages * 4096ULL);
    desc_avail = rt_virtqueue_desc_size(size) + rt_virtqueue_avail_size(size);
    *desc = ring;
    *avail = ring + rt_virtqueue_desc_size(size);
    *used = ring + ((desc_avail + 4095ULL) & ~4095ULL);
    *qsize = size;
    rt_io_write32(bar0, RT_VIRTIO_PCI_QUEUE_PFN, (spl_u32)(ring >> 12));
    return 0;
}


static void rt_pci_scan_qemu_virt(void) {
    g_rt_pci_count = 0;
    for (spl_u64 dev = 0; dev < 32 && g_rt_pci_count < RT_PCI_MAX_DEVICES; dev = dev + 1) {
        spl_u32 id = rt_pci_read_config32(0, dev, 0, 0);
        spl_u32 class_reg;
        spl_u32 bar0;
        RtPciDevice *out;
        if ((id & 0xffffU) == 0xffffU) {
            continue;
        }
        class_reg = rt_pci_read_config32(0, dev, 0, 8);
        bar0 = rt_pci_read_config32(0, dev, 0, 0x10);
        out = &g_rt_pci_devices[g_rt_pci_count];
        out->bus = 0;
        out->device = (spl_i64)dev;
        out->function = 0;
        out->class_code = (spl_i64)((class_reg >> 24) & 0xffU);
        out->subclass = (spl_i64)((class_reg >> 16) & 0xffU);
        out->vendor = (spl_i64)(id & 0xffffU);
        out->device_id = (spl_i64)((id >> 16) & 0xffffU);
        out->bar0 = (spl_i64)(bar0 & ~0xfU);
        out->irq = 0;
        g_rt_pci_count = g_rt_pci_count + 1;
    }
}

static spl_i64 rt_pci_is_virtio_net(spl_i64 cls, spl_i64 sub, spl_i64 vendor, spl_i64 device_id) {
    if (cls != 2 || sub != 0) {
        return 0;
    }
    if (vendor != RT_VIRTIO_VENDOR_ID) {
        return 0;
    }
    if (device_id == RT_VIRTIO_NET_LEGACY_DEVICE_ID ||
        device_id == RT_VIRTIO_NET_MODERN_DEVICE_ID) {
        return 1;
    }
    return 0;
}

static spl_i64 rt_pci_is_virtio_gpu(spl_i64 cls, spl_i64 sub, spl_i64 vendor, spl_i64 device_id) {
    if (vendor != RT_VIRTIO_VENDOR_ID) {
        return 0;
    }
    if (device_id == RT_VIRTIO_GPU_LEGACY_DEVICE_ID) {
        return 1;
    }
    if (device_id == RT_VIRTIO_GPU_MODERN_DEVICE_ID) {
        (void)cls;
        (void)sub;
        return 1;
    }
    return 0;
}

static spl_i64 rt_pci_is_virtio_blk(spl_i64 vendor, spl_i64 device_id) {
    if (vendor != RT_VIRTIO_VENDOR_ID) {
        return 0;
    }
    if (device_id == RT_VIRTIO_BLK_LEGACY_DEVICE_ID ||
        device_id == RT_VIRTIO_BLK_MODERN_DEVICE_ID) {
        return 1;
    }
    return 0;
}

/* Little-endian pack/unpack for the VirtIO control queue. freestanding_runtime.c
 * declared these three twice (once extern near the top, once static here) and
 * DEFINED them nowhere, which is one of the reasons that file has never
 * compiled. VirtIO structures are little-endian by spec and riscv64 is
 * little-endian, but these stay byte-explicit rather than casting through a
 * wider pointer, so they are alignment-safe on the packed command buffer. */
static void rt_put_le32(spl_u8 *p, spl_u32 v) {
    p[0] = (spl_u8)(v & 0xffU);
    p[1] = (spl_u8)((v >> 8) & 0xffU);
    p[2] = (spl_u8)((v >> 16) & 0xffU);
    p[3] = (spl_u8)((v >> 24) & 0xffU);
}

static void rt_put_le64(spl_u8 *p, spl_u64 v) {
    for (spl_u64 i = 0; i < 8ULL; i = i + 1ULL) {
        p[i] = (spl_u8)((v >> (i * 8ULL)) & 0xffULL);
    }
}

static spl_u32 rt_get_le32(const spl_u8 *p) {
    return (spl_u32)p[0]
         | ((spl_u32)p[1] << 8)
         | ((spl_u32)p[2] << 16)
         | ((spl_u32)p[3] << 24);
}

spl_i64 rt_pci_device_count(void) {
    if (g_rt_pci_count < 0) {
        rt_pci_scan_qemu_virt();
    }
    return g_rt_pci_count;
}

spl_i64 rt_pci_get_field(spl_i64 index, spl_i64 field) {
    RtPciDevice *dev;
    if (g_rt_pci_count < 0) {
        rt_pci_scan_qemu_virt();
    }
    if (index < 0 || index >= g_rt_pci_count) {
        return -1;
    }
    dev = &g_rt_pci_devices[index];
    if (field == 0) return dev->bus;
    if (field == 1) return dev->device;
    if (field == 2) return dev->function;
    if (field == 3) return dev->class_code;
    if (field == 4) return dev->subclass;
    if (field == 5) return dev->vendor;
    if (field == 6) return dev->device_id;
    if (field == 7) return dev->bar0;
    if (field == 8) return dev->irq;
    return -1;
}


static void rt_gpu_ctrl_hdr(spl_u8 *p, spl_u32 cmd) {
    rt_memzero(p, 64);
    rt_put_le32(p, cmd);
}

static spl_i64 rt_gpu_send_command(spl_u32 cmd, spl_u32 req_len, spl_u32 resp_len) {
    volatile spl_u16 *used_idx;
    spl_u16 start;
    if ((!g_rt_gpu_modern && !g_rt_gpu_bar0) || !g_rt_gpu_cmd || !g_rt_gpu_resp || g_rt_gpu_qsize < 2) {
        return -1;
    }
    rt_desc_write(g_rt_gpu_desc, 0, g_rt_gpu_cmd, req_len, RT_VIRTQ_DESC_F_NEXT, 1);
    rt_desc_write(g_rt_gpu_desc, 1, g_rt_gpu_resp, resp_len, RT_VIRTQ_DESC_F_WRITE, 0);
    rt_memzero((void *)g_rt_gpu_resp, resp_len);
    rt_avail_push(g_rt_gpu_avail, g_rt_gpu_qsize, 0);
    used_idx = (volatile spl_u16 *)(g_rt_gpu_used + 2ULL);
    start = *used_idx;
    __sync_synchronize();
    if (g_rt_gpu_modern) {
        rt_mmio_write16_raw(g_rt_gpu_notify + ((spl_u64)g_rt_gpu_notify_off * (spl_u64)g_rt_gpu_notify_multiplier), 0);
    } else {
        rt_io_write16(g_rt_gpu_bar0, RT_VIRTIO_PCI_QUEUE_NOTIFY, 0);
    }
    for (spl_u64 polls = 0; polls < 1000000ULL; polls = polls + 1) {
        __sync_synchronize();
        if (*used_idx != start) {
            g_rt_gpu_last_used = *used_idx;
            return (spl_i64)rt_get_le32((const spl_u8 *)g_rt_gpu_resp);
        }
    }
    (void)cmd;
    return -2;
}

static spl_i64 rt_gpu_find_modern_caps(RtPciDevice *dev) {
    spl_u8 cap = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x34) & 0xfcU;
    spl_u64 bar_base[6];
    for (spl_u64 i = 0; i < 6; i = i + 1) {
        bar_base[i] = 0;
    }
    bar_base[1] = RT_PCI_MMIO_BASE + ((spl_u64)dev->device * 0x100000ULL);
    bar_base[4] = RT_PCI_MMIO_BASE + ((spl_u64)dev->device * 0x100000ULL) + 0x10000ULL;
    rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x14, (spl_u32)bar_base[1]);
    rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x20, (spl_u32)bar_base[4]);
    rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x24, 0);
    rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x04, RT_PCI_CMD_MEM | RT_PCI_CMD_BUS_MASTER);
    while (cap >= 0x40U && cap != 0xffU) {
        spl_u8 cap_id = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap);
        spl_u8 next = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 1U) & 0xfcU;
        if (cap_id == RT_PCI_CAP_ID_VENDOR_SPECIFIC) {
            spl_u8 cfg_type = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 3U);
            spl_u8 bar = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 4U);
            spl_u32 offset = rt_pci_read_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 8U);
            if (bar < 6U && bar_base[bar] != 0) {
                if (cfg_type == RT_VIRTIO_PCI_CAP_COMMON_CFG) {
                    g_rt_gpu_common = bar_base[bar] + offset;
                } else if (cfg_type == RT_VIRTIO_PCI_CAP_NOTIFY_CFG) {
                    g_rt_gpu_notify = bar_base[bar] + offset;
                    g_rt_gpu_notify_multiplier = rt_pci_read_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 16U);
                }
            }
        }
        if (next == 0 || next == cap) {
            break;
        }
        cap = next;
    }
    if (g_rt_gpu_common == 0 || g_rt_gpu_notify == 0 || g_rt_gpu_notify_multiplier == 0) {
        return -1;
    }
    return 0;
}

static spl_i64 rt_gpu_setup_modern(RtPciDevice *dev) {
    spl_u16 max_size;
    spl_u16 size;
    spl_u64 total;
    spl_u64 pages;
    spl_u64 ring;
    spl_u64 desc_avail;
    if (rt_gpu_find_modern_caps(dev) < 0) {
        return -1;
    }
    rt_mmio_write8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS, 0);
    rt_mmio_write8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE);
    rt_mmio_write8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DRIVER_FEATURE_SELECT, 0);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DRIVER_FEATURE, 0);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DRIVER_FEATURE_SELECT, 1);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DRIVER_FEATURE, 1);
    rt_mmio_write8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK);
    if ((rt_mmio_read8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS) & RT_VIRTIO_STATUS_FEATURES_OK) == 0) {
        return -2;
    }
    rt_mmio_write16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_SELECT, 0);
    if (rt_mmio_read16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_NUM_QUEUES) == 0) {
        return -3;
    }
    max_size = rt_mmio_read16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_SIZE);
    if (max_size == 0) {
        return -4;
    }
    size = max_size > RT_GPU_QUEUE_CAP ? RT_GPU_QUEUE_CAP : max_size;
    total = rt_virtqueue_total_size(size);
    pages = (total + 4095ULL) / 4096ULL;
    ring = rt_alloc_contiguous_pages(pages);
    if (ring == 0) {
        return -5;
    }
    rt_memzero((void *)ring, pages * 4096ULL);
    desc_avail = rt_virtqueue_desc_size(size) + rt_virtqueue_avail_size(size);
    g_rt_gpu_desc = ring;
    g_rt_gpu_avail = ring + rt_virtqueue_desc_size(size);
    g_rt_gpu_used = ring + ((desc_avail + 4095ULL) & ~4095ULL);
    g_rt_gpu_qsize = size;
    rt_mmio_write16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_SIZE, size);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DESC_LO, (spl_u32)(g_rt_gpu_desc & 0xffffffffULL));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DESC_HI, (spl_u32)(g_rt_gpu_desc >> 32));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DRIVER_LO, (spl_u32)(g_rt_gpu_avail & 0xffffffffULL));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DRIVER_HI, (spl_u32)(g_rt_gpu_avail >> 32));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DEVICE_LO, (spl_u32)(g_rt_gpu_used & 0xffffffffULL));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DEVICE_HI, (spl_u32)(g_rt_gpu_used >> 32));
    g_rt_gpu_notify_off = rt_mmio_read16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_NOTIFY_OFF);
    rt_mmio_write16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_ENABLE, 1);
    rt_mmio_write8_raw(
        g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS,
        RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK | RT_VIRTIO_STATUS_DRIVER_OK
    );
    g_rt_gpu_modern = 1;
    return 0;
}

static spl_i64 rt_gpu_cmd_get_display_info(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    spl_i64 resp;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_GET_DISPLAY_INFO);
    resp = rt_gpu_send_command(RT_GPU_CMD_GET_DISPLAY_INFO, 24U, 408U);
    if (resp == RT_GPU_RESP_OK_DISPLAY_INFO) {
        return 0;
    }
    if (resp < 0) {
        return resp;
    }
    return -3;
}

static spl_i64 rt_gpu_cmd_resource_create(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_RESOURCE_CREATE_2D);
    rt_put_le32(cmd + 24, RT_GPU_RESOURCE_ID);
    rt_put_le32(cmd + 28, RT_GPU_FORMAT_B8G8R8A8_UNORM);
    rt_put_le32(cmd + 32, RT_GPU_WIDTH);
    rt_put_le32(cmd + 36, RT_GPU_HEIGHT);
    return rt_gpu_send_command(RT_GPU_CMD_RESOURCE_CREATE_2D, 40U, 24U) == RT_GPU_RESP_OK_NODATA ? 0 : -1;
}

static spl_i64 rt_gpu_cmd_attach_backing(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_RESOURCE_ATTACH_BACKING);
    rt_put_le32(cmd + 24, RT_GPU_RESOURCE_ID);
    rt_put_le32(cmd + 28, 1U);
    rt_put_le64(cmd + 32, g_rt_gpu_fb);
    rt_put_le32(cmd + 40, RT_GPU_WIDTH * RT_GPU_HEIGHT * 4U);
    rt_put_le32(cmd + 44, 0U);
    return rt_gpu_send_command(RT_GPU_CMD_RESOURCE_ATTACH_BACKING, 48U, 24U) == RT_GPU_RESP_OK_NODATA ? 0 : -1;
}

static spl_i64 rt_gpu_cmd_set_scanout(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_SET_SCANOUT);
    rt_put_le32(cmd + 24, 0U);
    rt_put_le32(cmd + 28, 0U);
    rt_put_le32(cmd + 32, RT_GPU_WIDTH);
    rt_put_le32(cmd + 36, RT_GPU_HEIGHT);
    rt_put_le32(cmd + 40, 0U);
    rt_put_le32(cmd + 44, RT_GPU_RESOURCE_ID);
    return rt_gpu_send_command(RT_GPU_CMD_SET_SCANOUT, 48U, 24U) == RT_GPU_RESP_OK_NODATA ? 0 : -1;
}

static spl_i64 rt_gpu_cmd_transfer_flush(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    spl_i64 resp;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_TRANSFER_TO_HOST_2D);
    rt_put_le32(cmd + 24, 0U);
    rt_put_le32(cmd + 28, 0U);
    rt_put_le32(cmd + 32, RT_GPU_WIDTH);
    rt_put_le32(cmd + 36, RT_GPU_HEIGHT);
    rt_put_le64(cmd + 40, 0ULL);
    rt_put_le32(cmd + 48, RT_GPU_RESOURCE_ID);
    rt_put_le32(cmd + 52, 0U);
    resp = rt_gpu_send_command(RT_GPU_CMD_TRANSFER_TO_HOST_2D, 56U, 24U);
    if (resp != RT_GPU_RESP_OK_NODATA) {
        return -1;
    }
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_RESOURCE_FLUSH);
    rt_put_le32(cmd + 24, 0U);
    rt_put_le32(cmd + 28, 0U);
    rt_put_le32(cmd + 32, RT_GPU_WIDTH);
    rt_put_le32(cmd + 36, RT_GPU_HEIGHT);
    rt_put_le32(cmd + 40, RT_GPU_RESOURCE_ID);
    rt_put_le32(cmd + 44, 0U);
    return rt_gpu_send_command(RT_GPU_CMD_RESOURCE_FLUSH, 48U, 24U) == RT_GPU_RESP_OK_NODATA ? 0 : -1;
}

static void rt_gpu_fill_rect(spl_u32 x, spl_u32 y, spl_u32 w, spl_u32 h, spl_u32 color) {
    volatile spl_u32 *fb = (volatile spl_u32 *)g_rt_gpu_fb;
    spl_u32 max_x = x + w;
    spl_u32 max_y = y + h;
    if (max_x > RT_GPU_WIDTH) {
        max_x = RT_GPU_WIDTH;
    }
    if (max_y > RT_GPU_HEIGHT) {
        max_y = RT_GPU_HEIGHT;
    }
    for (spl_u32 py = y; py < max_y; py = py + 1U) {
        for (spl_u32 px = x; px < max_x; px = px + 1U) {
            fb[(spl_u64)py * RT_GPU_WIDTH + px] = color;
        }
    }
}

static void rt_gpu_fill_wm_anchor_scene(void) {
    rt_gpu_fill_rect(0U, 0U, RT_GPU_WIDTH, RT_GPU_HEIGHT, 0xff101418U);
    rt_gpu_fill_rect(0U, 0U, RT_GPU_WIDTH, 24U, 0xff1f2937U);
    rt_gpu_fill_rect(24U, 36U, 128U, 20U, 0xff4f46e5U);
    rt_gpu_fill_rect(24U, 56U, 128U, 72U, 0xfff8fafcU);
    rt_gpu_fill_rect(168U, 48U, 112U, 88U, 0xff0f766eU);
    rt_gpu_fill_rect(0U, 212U, RT_GPU_WIDTH, 28U, 0xff22c55eU);
}

/* The RISC-V virtio scanout does not expose the generic direct-LFB array ABI
 * yet. Returning zero keeps FramebufferDriver on its exact portable fallback
 * instead of falsely claiming that a row was presented. */
spl_u64 rt_gui_blend_span4(spl_u64 xy, spl_u64 src, spl_u64 src_offset,
                           spl_u64 count) {
    (void)xy;
    (void)src;
    (void)src_offset;
    (void)count;
    return 0ULL;
}

spl_i64 rt_gui_flush(void) {
    if (!g_rt_display_ready || !g_rt_gpu_fb) {
        return -1;
    }
    return rt_gpu_cmd_transfer_flush();
}

static void rt_gpu_fill_wm_scene(void) {
    volatile spl_u32 *fb = (volatile spl_u32 *)g_rt_gpu_fb;
    for (spl_u32 y = 0; y < RT_GPU_HEIGHT; y = y + 1U) {
        for (spl_u32 x = 0; x < RT_GPU_WIDTH; x = x + 1U) {
            spl_u8 r = (spl_u8)(x & 0xffU);
            spl_u8 g = (spl_u8)(y & 0xffU);
            spl_u8 b = (spl_u8)((x ^ y) & 0xffU);
            fb[(spl_u64)y * RT_GPU_WIDTH + x] = 0xff000000U | ((spl_u32)r << 16) | ((spl_u32)g << 8) | (spl_u32)b;
        }
    }
}

spl_i64 rt_display_init(void) {
    spl_i64 count = rt_pci_device_count();
    for (spl_i64 i = 0; i < count; i = i + 1) {
        spl_i64 cls = rt_pci_get_field(i, 3);
        spl_i64 sub = rt_pci_get_field(i, 4);
        spl_i64 vendor = rt_pci_get_field(i, 5);
        spl_i64 device_id = rt_pci_get_field(i, 6);
        if (rt_pci_is_virtio_gpu(cls, sub, vendor, device_id)) {
            RtPciDevice *dev = &g_rt_pci_devices[i];
            g_rt_gpu_modern = 0;
            if (device_id == RT_VIRTIO_GPU_MODERN_DEVICE_ID) {
                if (rt_gpu_setup_modern(dev) < 0) {
                    g_rt_display_ready = 0;
                    return -2;
                }
            } else {
                rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x10, (spl_u32)(RT_PCI_LEGACY_GPU_IO_PORT | 1ULL));
                rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x04, RT_PCI_CMD_IO | RT_PCI_CMD_MEM | RT_PCI_CMD_BUS_MASTER);
                g_rt_gpu_bar0 = RT_PCI_IO_BASE + RT_PCI_LEGACY_GPU_IO_PORT;
                rt_io_write8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS, 0);
                rt_io_write8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE);
                rt_io_write8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER);
                rt_io_write32(g_rt_gpu_bar0, RT_VIRTIO_PCI_GUEST_FEATURES, 0);
                rt_io_write8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK);
                if ((rt_io_read8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS) & RT_VIRTIO_STATUS_FEATURES_OK) == 0) {
                    g_rt_display_ready = 0;
                    return -3;
                }
                if (rt_setup_virtqueue_capped(g_rt_gpu_bar0, 0, RT_GPU_QUEUE_CAP, &g_rt_gpu_desc, &g_rt_gpu_avail, &g_rt_gpu_used, &g_rt_gpu_qsize) < 0) {
                    g_rt_display_ready = 0;
                    return -4;
                }
                rt_io_write8(
                    g_rt_gpu_bar0,
                    RT_VIRTIO_PCI_STATUS,
                    RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK | RT_VIRTIO_STATUS_DRIVER_OK
                );
            }
            g_rt_gpu_cmd = spl_riscv_noalloc_alloc_page();
            g_rt_gpu_resp = spl_riscv_noalloc_alloc_page();
            g_rt_gpu_fb = rt_alloc_contiguous_pages((RT_GPU_WIDTH * RT_GPU_HEIGHT * 4ULL + 4095ULL) / 4096ULL);
            if (!g_rt_gpu_cmd || !g_rt_gpu_resp || !g_rt_gpu_fb) {
                g_rt_display_ready = 0;
                return -5;
            }
            rt_memzero((void *)g_rt_gpu_cmd, 4096ULL);
            rt_memzero((void *)g_rt_gpu_resp, 4096ULL);
            rt_memzero((void *)g_rt_gpu_fb, RT_GPU_WIDTH * RT_GPU_HEIGHT * 4ULL);
            spl_i64 display_info_rc = rt_gpu_cmd_get_display_info();
            if (display_info_rc < 0) {
                g_rt_display_ready = 0;
                return -610 + display_info_rc;
            }
            if (rt_gpu_cmd_resource_create() < 0) {
                g_rt_display_ready = 0;
                return -62;
            }
            if (rt_gpu_cmd_attach_backing() < 0) {
                g_rt_display_ready = 0;
                return -63;
            }
            if (rt_gpu_cmd_set_scanout() < 0) {
                g_rt_display_ready = 0;
                return -64;
            }
            g_rt_display_ready = 1;
            return 0;
        }
    }
    g_rt_display_ready = 0;
    return -1;
}

spl_i64 rt_display_width(void) {
    return g_rt_display_ready ? RT_GPU_WIDTH : 0;
}

spl_i64 rt_display_height(void) {
    return g_rt_display_ready ? RT_GPU_HEIGHT : 0;
}

/* The four accessors os.kernel.arch.riscv64.display declares as extern and no
 * C in this tree ever defined. Each reports state this driver already
 * establishes above -- none of them invents a value:
 *   pitch  -- the scanout is created as RT_GPU_WIDTH x RT_GPU_HEIGHT in
 *             RT_GPU_FORMAT_B8G8R8A8_UNORM, so the stride is width * 4.
 *   bpp    -- B8G8R8A8_UNORM is 32 bits per pixel.
 *   framebuffer_address -- g_rt_gpu_fb, the contiguous backing this driver
 *             allocated and attached to the resource.
 *   present -- transfer-to-host-2d + resource-flush, which is exactly
 *             rt_gpu_cmd_transfer_flush(); it already returns 0 on success and
 *             -1 otherwise, the contract display.spl checks (`== 0`).
 * All four fail closed while the display is not ready, so a caller cannot read
 * a plausible-looking value out of an un-initialised scanout. */
spl_i64 rt_display_pitch(void) {
    return g_rt_display_ready ? (spl_i64)(RT_GPU_WIDTH * 4U) : 0;
}

spl_i64 rt_display_bpp(void) {
    return g_rt_display_ready ? 32 : 0;
}

spl_u64 rt_display_framebuffer_address(void) {
    return g_rt_display_ready ? g_rt_gpu_fb : 0ULL;
}

spl_i64 rt_display_present(void) {
    if (!g_rt_display_ready || !g_rt_gpu_fb) {
        return -1;
    }
    return rt_gpu_cmd_transfer_flush();
}
