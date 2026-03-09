/**
 * host_dbc_daemon.cpp - Host DBC Daemon for Module 56
 *
 * This daemon implements the host DBC mechanism (Module 55.3):
 * - Polls shadow doorbell buffer in host memory (pinned, GPU-accessible)
 * - Detects changes from GPU kernel writes
 * - Rings actual NVMe MMIO doorbells when shadow buffer changes
 *
 * Architecture:
 *   GPU Kernel → Writes shadow_doorbells[qid] (host memory via PCIe)
 *   This Daemon → Polls shadow_doorbells[qid] (local host memory access)
 *   This Daemon → Writes NVMe MMIO doorbell registers
 *   NVMe Controller → Processes commands from SQ
 *
 * Usage:
 *   ./host_dbc_daemon --device /dev/nvme0 --qid 1 --shadow-buffer <addr>
 */

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <unistd.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <signal.h>
#include <atomic>
#include <thread>
#include <chrono>
#include <getopt.h>
#include <cuda_runtime.h>

// Daemon configuration
struct DaemonConfig {
    const char* device_path;           // NVMe device path (e.g., /dev/nvme0)
    uint16_t qid;                      // Queue ID
    volatile uint32_t* shadow_db_host;  // Shadow doorbell buffer (HOST pointer for CPU access)
    volatile uint32_t* nvme_sq_db;     // NVMe SQ doorbell MMIO address
    volatile uint32_t* nvme_cq_db;     // NVMe CQ doorbell MMIO address
    uint32_t poll_interval_us;         // Polling interval in microseconds
    uint16_t sq_depth;                 // SQ depth (for wrapping)
    uint16_t cq_depth;                 // CQ depth (for wrapping)
    void* bar0_base;                   // Mapped BAR0 base
    size_t bar0_size;                  // BAR0 size
    int nvme_fd;                       // NVMe device file descriptor
};

// Global daemon state
static std::atomic<bool> g_running(false);
static DaemonConfig g_config = {};  // Initialize to zeros

// Statistics
struct DaemonStats {
    std::atomic<uint64_t> poll_count{0};
    std::atomic<uint64_t> sq_doorbell_rings{0};
    std::atomic<uint64_t> cq_doorbell_rings{0};
    std::atomic<uint32_t> last_sq_tail{0};
    std::atomic<uint32_t> last_cq_head{0};
};

static DaemonStats g_stats;

/**
 * Signal handler for graceful shutdown
 */
void signal_handler(int signum) {
    printf("\n[Daemon] Received signal %d, shutting down...\n", signum);
    g_running.store(false);
}

/**
 * Map NVMe BAR0 for doorbell access
 *
 * This requires either:
 * - VFIO mapping (preferred, safer)
 * - /dev/mem mapping (requires root, dangerous)
 * - kernel module providing /dev/gpu_p2p_nvme
 */
int map_nvme_doorbells(DaemonConfig* config) {
    printf("[Daemon] Mapping NVMe doorbells for %s QID %u...\n",
           config->device_path, config->qid);

    // Map NVMe PCI BAR0 using sysfs resource file
    // This gives us direct access to MMIO registers

    // Convert /dev/nvmeX to PCI address
    // For now, assume nvme0 -> 0000:41:00.0 (would need proper lookup in production)
    const char* pci_address = "0000:41:00.0";
    char resource_path[256];
    snprintf(resource_path, sizeof(resource_path),
             "/sys/bus/pci/devices/%s/resource0", pci_address);

    // Open PCI BAR0 resource file
    int fd = open(resource_path, O_RDWR | O_SYNC);
    if (fd < 0) {
        perror("open resource0");
        fprintf(stderr, "[Daemon] Failed to open %s\n", resource_path);
        fprintf(stderr, "[Daemon] Make sure you have permissions (run with sudo)\n");
        return -1;
    }

    // Get resource size
    struct stat st;
    if (fstat(fd, &st) < 0) {
        perror("fstat");
        close(fd);
        return -1;
    }
    size_t bar_size = st.st_size;

    // Map BAR0 into our address space
    void* bar0 = mmap(NULL, bar_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (bar0 == MAP_FAILED) {
        perror("mmap");
        close(fd);
        return -1;
    }

    config->nvme_fd = fd;
    config->bar0_base = bar0;
    config->bar0_size = bar_size;

    // Calculate doorbell offsets
    // NVMe spec: Doorbells at BAR0 + 0x1000 + (2*qid + X) * (4 << DSTRD)
    // DSTRD = Doorbell Stride (usually 0, meaning 4 bytes between doorbells)
    // For now, assume DSTRD = 0
    const size_t DOORBELL_BASE = 0x1000;
    const size_t DSTRD = 0;  // Doorbell stride (0 = 4 bytes)
    const size_t doorbell_stride = 4 << DSTRD;

    size_t sq_db_offset = DOORBELL_BASE + (2 * config->qid) * doorbell_stride;
    size_t cq_db_offset = DOORBELL_BASE + (2 * config->qid + 1) * doorbell_stride;

    config->nvme_sq_db = (volatile uint32_t*)((char*)bar0 + sq_db_offset);
    config->nvme_cq_db = (volatile uint32_t*)((char*)bar0 + cq_db_offset);

    printf("[Daemon] Mapped BAR0: %p (size: %zu bytes)\n", bar0, bar_size);
    printf("[Daemon] SQ doorbell (QID %u): %p (offset: 0x%zx)\n",
           config->qid, config->nvme_sq_db, sq_db_offset);
    printf("[Daemon] CQ doorbell (QID %u): %p (offset: 0x%zx)\n",
           config->qid, config->nvme_cq_db, cq_db_offset);

    return 0;
}

/**
 * Unmap NVMe doorbells
 */
void unmap_nvme_doorbells(DaemonConfig* config) {
    if (config->bar0_base) {
        munmap(config->bar0_base, config->bar0_size);
        config->bar0_base = nullptr;
    }
    if (config->nvme_fd >= 0) {
        close(config->nvme_fd);
        config->nvme_fd = -1;
    }
    config->nvme_sq_db = nullptr;
    config->nvme_cq_db = nullptr;
}

/**
 * Ring SQ doorbell (MMIO write)
 */
void ring_sq_doorbell(DaemonConfig* config, uint16_t new_tail) {
    if (config->nvme_sq_db) {
        *config->nvme_sq_db = new_tail;
        __sync_synchronize();  // Memory barrier
        g_stats.sq_doorbell_rings.fetch_add(1);
    }
}

/**
 * Ring CQ doorbell (MMIO write)
 */
void ring_cq_doorbell(DaemonConfig* config, uint16_t new_head) {
    if (config->nvme_cq_db) {
        *config->nvme_cq_db = new_head;
        __sync_synchronize();  // Memory barrier
        g_stats.cq_doorbell_rings.fetch_add(1);
    }
}

/**
 * Main polling loop
 */
void polling_loop(DaemonConfig* config) {
    printf("[Daemon] Starting polling loop (interval: %u us)\n", config->poll_interval_us);

    uint32_t last_sq_shadow = 0;
    uint32_t last_cq_shadow = 0;

    // Shadow doorbell buffer layout: [SQ0, CQ0, SQ1, CQ1, SQ2, CQ2, ...]
    volatile uint32_t* sq_shadow = &config->shadow_db_host[2 * config->qid];
    volatile uint32_t* cq_shadow = &config->shadow_db_host[2 * config->qid + 1];

    while (g_running.load()) {
        g_stats.poll_count.fetch_add(1);

        // Read shadow doorbells directly from pinned host memory
        // This is safe - cudaHostAlloc creates memory accessible from both CPU and GPU
        // CPU reads using host pointer, GPU writes using device pointer
        uint32_t current_sq_shadow = *sq_shadow;
        uint32_t current_cq_shadow = *cq_shadow;

        // Check if SQ shadow doorbell changed
        if (current_sq_shadow != last_sq_shadow) {
            uint16_t new_tail = current_sq_shadow % config->sq_depth;

            printf("[Daemon] SQ shadow changed: %u → %u (wrapped: %u)\n",
                   last_sq_shadow, current_sq_shadow, new_tail);

            // Ring actual NVMe MMIO doorbell
            ring_sq_doorbell(config, new_tail);

            last_sq_shadow = current_sq_shadow;
            g_stats.last_sq_tail.store(new_tail);
        }

        // Check if CQ shadow doorbell changed
        if (current_cq_shadow != last_cq_shadow) {
            uint16_t new_head = current_cq_shadow % config->cq_depth;

            printf("[Daemon] CQ shadow changed: %u → %u (wrapped: %u)\n",
                   last_cq_shadow, current_cq_shadow, new_head);

            // Ring actual NVMe MMIO doorbell
            ring_cq_doorbell(config, new_head);

            last_cq_shadow = current_cq_shadow;
            g_stats.last_cq_head.store(new_head);
        }

        // Sleep for polling interval
        std::this_thread::sleep_for(std::chrono::microseconds(config->poll_interval_us));
    }

    printf("[Daemon] Polling loop exited\n");
}

/**
 * Print daemon statistics
 */
void print_stats() {
    printf("\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("Daemon Statistics:\n");
    printf("───────────────────────────────────────────────────────────────\n");
    printf("  Poll iterations:      %lu\n", g_stats.poll_count.load());
    printf("  SQ doorbells rung:    %lu\n", g_stats.sq_doorbell_rings.load());
    printf("  CQ doorbells rung:    %lu\n", g_stats.cq_doorbell_rings.load());
    printf("  Last SQ tail:         %u\n", g_stats.last_sq_tail.load());
    printf("  Last CQ head:         %u\n", g_stats.last_cq_head.load());
    printf("═══════════════════════════════════════════════════════════════\n");
}

/**
 * Print usage information
 */
void print_usage(const char* prog_name) {
    printf("Usage: %s [OPTIONS]\n", prog_name);
    printf("\n");
    printf("Host DBC Daemon for Module 56 (55.3 mode)\n");
    printf("\n");
    printf("Options:\n");
    printf("  --device PATH       NVMe device path (default: /dev/nvme0)\n");
    printf("  --qid NUM           Queue ID to monitor (default: 1)\n");
    printf("  --shadow PTR        Shadow doorbell buffer GPU address (hex)\n");
    printf("  --sq-depth NUM      SQ depth (default: 64)\n");
    printf("  --cq-depth NUM      CQ depth (default: 64)\n");
    printf("  --poll-interval US  Polling interval in microseconds (default: 10)\n");
    printf("  --help              Show this help message\n");
    printf("\n");
    printf("Example:\n");
    printf("  %s --device /dev/nvme0 --qid 1 --shadow 0x7f8a40000000\n", prog_name);
    printf("\n");
}

int main(int argc, char** argv) {
    // Default configuration
    g_config.device_path = "/dev/nvme0";
    g_config.qid = 1;
    g_config.shadow_db_host = nullptr;
    g_config.poll_interval_us = 10;
    g_config.sq_depth = 64;
    g_config.cq_depth = 64;

    // Parse command-line arguments
    static struct option long_options[] = {
        {"device", required_argument, 0, 'd'},
        {"qid", required_argument, 0, 'q'},
        {"shadow", required_argument, 0, 's'},
        {"sq-depth", required_argument, 0, 'S'},
        {"cq-depth", required_argument, 0, 'C'},
        {"poll-interval", required_argument, 0, 'p'},
        {"help", no_argument, 0, 'h'},
        {0, 0, 0, 0}
    };

    int opt;
    while ((opt = getopt_long(argc, argv, "d:q:s:S:C:p:h", long_options, nullptr)) != -1) {
        switch (opt) {
        case 'd':
            g_config.device_path = optarg;
            break;
        case 'q':
            g_config.qid = (uint16_t)atoi(optarg);
            break;
        case 's':
            g_config.shadow_db_host = (volatile uint32_t*)strtoull(optarg, nullptr, 16);
            break;
        case 'S':
            g_config.sq_depth = (uint16_t)atoi(optarg);
            break;
        case 'C':
            g_config.cq_depth = (uint16_t)atoi(optarg);
            break;
        case 'p':
            g_config.poll_interval_us = (uint32_t)atoi(optarg);
            break;
        case 'h':
            print_usage(argv[0]);
            return 0;
        default:
            print_usage(argv[0]);
            return 1;
        }
    }

    // Validate configuration
    if (!g_config.shadow_db_host) {
        fprintf(stderr, "Error: --shadow option is required\n");
        fprintf(stderr, "Get shadow buffer HOST address from DoorbellModeConfig.shadow_doorbells_host\n");
        fprintf(stderr, "NOTE: Use HOST pointer, not device pointer!\n");
        print_usage(argv[0]);
        return 1;
    }

    // Print configuration
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("Host DBC Daemon Starting\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  Device:           %s\n", g_config.device_path);
    printf("  Queue ID:         %u\n", g_config.qid);
    printf("  Shadow buffer (host): %p\n", g_config.shadow_db_host);
    printf("  SQ depth:         %u\n", g_config.sq_depth);
    printf("  CQ depth:         %u\n", g_config.cq_depth);
    printf("  Poll interval:    %u µs\n", g_config.poll_interval_us);
    printf("═══════════════════════════════════════════════════════════════\n");

    // Register signal handlers
    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);

    // Map NVMe doorbells
    if (map_nvme_doorbells(&g_config) != 0) {
        fprintf(stderr, "Error: Failed to map NVMe doorbells\n");
        return 1;
    }

    // Start daemon
    g_running.store(true);
    printf("[Daemon] Started successfully\n");
    printf("[Daemon] Press Ctrl+C to stop\n\n");

    // Run polling loop
    polling_loop(&g_config);

    // Cleanup
    printf("[Daemon] Cleaning up...\n");
    unmap_nvme_doorbells(&g_config);

    // Print final statistics
    print_stats();

    printf("[Daemon] Exited\n");
    return 0;
}
