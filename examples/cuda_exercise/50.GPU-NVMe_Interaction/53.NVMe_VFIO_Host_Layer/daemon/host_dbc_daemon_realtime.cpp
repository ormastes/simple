/**
 * host_dbc_daemon_realtime.cpp - Realtime Host DBC Daemon for Module 56
 *
 * This is a high-performance variant of the host DBC daemon with:
 * - Real-time scheduling (SCHED_FIFO)
 * - CPU affinity pinning to isolated core
 * - Busy-wait polling (no sleep) for lowest latency
 * - Memory locking to prevent page faults
 *
 * Performance target:
 * - Standard daemon (10µs polling): 12-50µs latency
 * - This realtime daemon: 4-8µs latency (3-6x improvement)
 *
 * Requirements:
 * - Root privileges (for real-time scheduling)
 * - Isolated CPU core (via isolcpus kernel parameter)
 * - Sufficient system resources (dedicated core at 100% CPU)
 *
 * Architecture:
 *   GPU Kernel → Writes shadow_doorbells[qid] (host memory via PCIe)
 *   This Daemon → Busy-wait polls shadow_doorbells[qid] (no sleep!)
 *   This Daemon → Writes NVMe MMIO doorbell registers
 *   NVMe Controller → Processes commands from SQ
 *
 * Usage:
 *   sudo ./host_dbc_daemon_realtime --device /dev/nvme0 --qid 1 \
 *                                    --shadow <addr> --cpu 7 --priority 90
 *
 * Setup:
 *   1. Isolate CPU core: Add "isolcpus=7" to kernel cmdline
 *   2. Reboot system
 *   3. Run daemon as root on isolated core
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
#include <getopt.h>
#include <cuda_runtime.h>
#include <linux/limits.h>

// Real-time scheduling headers
#include <sched.h>
#include <pthread.h>
#include <errno.h>

// Daemon configuration
struct RealtimeDaemonConfig {
    const char* device_path;           // NVMe device path (e.g., /dev/nvme0)
    uint16_t qid;                      // Queue ID
    volatile uint32_t* shadow_db_gpu;  // Shadow doorbell buffer (host memory, GPU-accessible)
    volatile uint32_t* nvme_sq_db;     // NVMe SQ doorbell MMIO address
    volatile uint32_t* nvme_cq_db;     // NVMe CQ doorbell MMIO address
    uint16_t sq_depth;                 // SQ depth (for wrapping)
    uint16_t cq_depth;                 // CQ depth (for wrapping)
    int cpu_core;                      // CPU core to pin to
    int sched_priority;                // Real-time priority (1-99)
    void* bar0_base;                   // Mapped BAR0 base
    size_t bar0_size;                  // BAR0 size
    int nvme_fd;                       // NVMe device file descriptor
};

// Global daemon state
static std::atomic<bool> g_running(false);
static RealtimeDaemonConfig g_config = {0};

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
    printf("\n[RT-Daemon] Received signal %d, shutting down...\n", signum);
    g_running.store(false);
}

/**
 * Setup real-time scheduling
 *
 * This requires root privileges.
 * Sets SCHED_FIFO with specified priority.
 */
int setup_realtime_scheduling(int priority) {
    struct sched_param param;
    param.sched_priority = priority;

    if (sched_setscheduler(0, SCHED_FIFO, &param) != 0) {
        fprintf(stderr, "[RT-Daemon] ERROR: Failed to set SCHED_FIFO: %s\n", strerror(errno));
        fprintf(stderr, "[RT-Daemon] Hint: Run with sudo or set CAP_SYS_NICE capability\n");
        return -1;
    }

    printf("[RT-Daemon] Real-time scheduling enabled (SCHED_FIFO, priority %d)\n", priority);
    return 0;
}

/**
 * Pin process to specific CPU core
 */
int pin_to_cpu(int cpu_core) {
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    CPU_SET(cpu_core, &cpuset);

    if (pthread_setaffinity_np(pthread_self(), sizeof(cpuset), &cpuset) != 0) {
        fprintf(stderr, "[RT-Daemon] ERROR: Failed to set CPU affinity: %s\n", strerror(errno));
        return -1;
    }

    // Verify the CPU core is actually isolated
    // Check /sys/devices/system/cpu/isolated
    FILE* f = fopen("/sys/devices/system/cpu/isolated", "r");
    if (f) {
        char isolated[256] = {0};
        fgets(isolated, sizeof(isolated), f);
        fclose(f);

        printf("[RT-Daemon] Isolated CPUs: %s", isolated);
        printf("[RT-Daemon] Pinned to CPU core %d\n", cpu_core);

        // Warn if core is not isolated
        char core_str[16];
        snprintf(core_str, sizeof(core_str), "%d", cpu_core);
        if (strstr(isolated, core_str) == nullptr) {
            fprintf(stderr, "[RT-Daemon] WARNING: CPU %d may not be isolated!\n", cpu_core);
            fprintf(stderr, "[RT-Daemon] Add 'isolcpus=%d' to kernel cmdline for best performance\n", cpu_core);
        }
    } else {
        printf("[RT-Daemon] Pinned to CPU core %d (isolation status unknown)\n", cpu_core);
    }

    return 0;
}

/**
 * Lock all memory to prevent paging
 */
int lock_memory() {
    if (mlockall(MCL_CURRENT | MCL_FUTURE) != 0) {
        fprintf(stderr, "[RT-Daemon] ERROR: Failed to lock memory: %s\n", strerror(errno));
        fprintf(stderr, "[RT-Daemon] Hint: Check /etc/security/limits.conf for memlock limits\n");
        return -1;
    }

    printf("[RT-Daemon] Memory locked (no paging)\n");
    return 0;
}

/**
 * Map NVMe BAR0 for doorbell access
 *
 * This requires either:
 * - VFIO mapping (preferred, safer)
 * - /dev/mem mapping (requires root, dangerous)
 * - kernel module providing /dev/gpu_p2p_nvme
 */
int map_nvme_doorbells(RealtimeDaemonConfig* config) {
    printf("[RT-Daemon] Mapping NVMe doorbells for %s QID %u...\n",
           config->device_path, config->qid);

    // Derive PCI BDF from device path (/dev/nvmeX)
    // /sys/block/nvmeX/device -> ../../../0000:bb:dd.f/...
    char device_name[64] = {0};
    const char* slash = strrchr(config->device_path, '/');
    snprintf(device_name, sizeof(device_name), "%s", slash ? slash + 1 : config->device_path);

    char link_path[PATH_MAX] = {0};
    snprintf(link_path, sizeof(link_path), "/sys/block/%s/device", device_name);

    char bdf_link[PATH_MAX] = {0};
    ssize_t link_len = readlink(link_path, bdf_link, sizeof(bdf_link) - 1);
    if (link_len < 0) {
        perror("[RT-Daemon] readlink PCI path");
        return -1;
    }
    bdf_link[link_len] = '\0';

    // Extract BDF from symlink target
    const char* last_slash = strrchr(bdf_link, '/');
    const char* bdf = last_slash ? last_slash + 1 : bdf_link;

    char resource_path[PATH_MAX] = {0};
    snprintf(resource_path, sizeof(resource_path),
             "/sys/bus/pci/devices/%s/resource0", bdf);

    int fd = open(resource_path, O_RDWR | O_SYNC);
    if (fd < 0) {
        perror("[RT-Daemon] open resource0");
        fprintf(stderr, "[RT-Daemon] Failed to open %s\n", resource_path);
        fprintf(stderr, "[RT-Daemon] Ensure VFIO or proper permissions (root)\n");
        return -1;
    }

    struct stat st;
    if (fstat(fd, &st) < 0) {
        perror("[RT-Daemon] fstat");
        close(fd);
        return -1;
    }

    void* bar0 = mmap(nullptr, st.st_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (bar0 == MAP_FAILED) {
        perror("[RT-Daemon] mmap BAR0");
        close(fd);
        return -1;
    }

    config->nvme_fd = fd;
    config->bar0_base = bar0;
    config->bar0_size = st.st_size;

    const size_t DOORBELL_BASE = 0x1000;
    const size_t DSTRD = 0;
    const size_t stride = 4 << DSTRD;
    size_t sq_db_offset = DOORBELL_BASE + (2 * config->qid) * stride;
    size_t cq_db_offset = DOORBELL_BASE + (2 * config->qid + 1) * stride;

    config->nvme_sq_db = (volatile uint32_t*)((uint8_t*)bar0 + sq_db_offset);
    config->nvme_cq_db = (volatile uint32_t*)((uint8_t*)bar0 + cq_db_offset);

    printf("[RT-Daemon] BAR0 mapped @ %p (size=%zu)\n", bar0, (size_t)st.st_size);
    printf("[RT-Daemon] SQ doorbell @ %p (offset 0x%zx)\n",
           config->nvme_sq_db, sq_db_offset);
    printf("[RT-Daemon] CQ doorbell @ %p (offset 0x%zx)\n",
           config->nvme_cq_db, cq_db_offset);

    return 0;
}

/**
 * Unmap NVMe doorbells
 */
void unmap_nvme_doorbells(RealtimeDaemonConfig* config) {
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
 *
 * CRITICAL: This is a hot path - must be as fast as possible
 */
static inline void ring_sq_doorbell(RealtimeDaemonConfig* config, uint16_t new_tail) {
    if (config->nvme_sq_db) {
        *config->nvme_sq_db = new_tail;
        __sync_synchronize();  // Memory barrier (compiler + CPU)
        g_stats.sq_doorbell_rings.fetch_add(1, std::memory_order_relaxed);
    }
}

/**
 * Ring CQ doorbell (MMIO write)
 */
static inline void ring_cq_doorbell(RealtimeDaemonConfig* config, uint16_t new_head) {
    if (config->nvme_cq_db) {
        *config->nvme_cq_db = new_head;
        __sync_synchronize();  // Memory barrier
        g_stats.cq_doorbell_rings.fetch_add(1, std::memory_order_relaxed);
    }
}

/**
 * Realtime busy-wait polling loop
 *
 * KEY OPTIMIZATION: NO SLEEP!
 * This loop runs at 100% CPU on the isolated core for lowest latency.
 *
 * Expected latency:
 * - GPU write shadow DB: 2-5µs (PCIe write to host memory)
 * - This daemon detects: <1µs (busy-wait, immediate detection)
 * - MMIO write: ~2µs (BAR0 write)
 * - Total: 4-8µs (vs 12-50µs for standard daemon)
 */
void realtime_polling_loop(RealtimeDaemonConfig* config) {
    printf("[RT-Daemon] Starting busy-wait polling loop (NO SLEEP)\n");
    printf("[RT-Daemon] WARNING: This will consume 100%% CPU on core %d\n", config->cpu_core);

    uint32_t last_sq_shadow = 0;
    uint32_t last_cq_shadow = 0;

    // Shadow doorbell buffer layout: [SQ0, CQ0, SQ1, CQ1, SQ2, CQ2, ...]
    volatile uint32_t* sq_shadow = &config->shadow_db_gpu[2 * config->qid];
    volatile uint32_t* cq_shadow = &config->shadow_db_gpu[2 * config->qid + 1];

    // Print once at startup (avoid printf in hot loop)
    printf("[RT-Daemon] Monitoring: SQ shadow @ %p, CQ shadow @ %p\n", sq_shadow, cq_shadow);
    printf("[RT-Daemon] Entering hot loop...\n\n");

    // HOT LOOP - OPTIMIZE FOR MINIMAL LATENCY
    while (g_running.load(std::memory_order_relaxed)) {
        g_stats.poll_count.fetch_add(1, std::memory_order_relaxed);

        // Read shadow doorbells directly from host memory
        // No cudaMemcpy needed - this is pinned host memory accessible from CPU
        uint32_t current_sq_shadow = *sq_shadow;
        uint32_t current_cq_shadow = *cq_shadow;

        // Check if SQ shadow doorbell changed
        if (__builtin_expect(current_sq_shadow != last_sq_shadow, 0)) {
            uint16_t new_tail = current_sq_shadow % config->sq_depth;

            // Ring actual NVMe MMIO doorbell IMMEDIATELY
            ring_sq_doorbell(config, new_tail);

            last_sq_shadow = current_sq_shadow;
            g_stats.last_sq_tail.store(new_tail, std::memory_order_relaxed);
        }

        // Check if CQ shadow doorbell changed
        if (__builtin_expect(current_cq_shadow != last_cq_shadow, 0)) {
            uint16_t new_head = current_cq_shadow % config->cq_depth;

            // Ring actual NVMe MMIO doorbell IMMEDIATELY
            ring_cq_doorbell(config, new_head);

            last_cq_shadow = current_cq_shadow;
            g_stats.last_cq_head.store(new_head, std::memory_order_relaxed);
        }

        // NO SLEEP - busy wait for lowest latency!
        // This is intentional - we trade CPU usage for latency
    }

    printf("[RT-Daemon] Polling loop exited\n");
}

/**
 * Print daemon statistics
 */
void print_stats() {
    printf("\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("Realtime Daemon Statistics:\n");
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
    printf("Realtime Host DBC Daemon for Module 56 (55.3 mode)\n");
    printf("\n");
    printf("This daemon uses real-time scheduling and busy-wait polling for\n");
    printf("ultra-low latency doorbell forwarding (4-8µs vs 12-50µs standard).\n");
    printf("\n");
    printf("REQUIREMENTS:\n");
    printf("  - Root privileges (for SCHED_FIFO)\n");
    printf("  - Isolated CPU core (via isolcpus kernel parameter)\n");
    printf("  - Dedicated core at 100%% CPU usage\n");
    printf("\n");
    printf("Options:\n");
    printf("  --device PATH       NVMe device path (default: /dev/nvme0)\n");
    printf("  --qid NUM           Queue ID to monitor (default: 1)\n");
    printf("  --shadow PTR        Shadow doorbell buffer address (hex)\n");
    printf("  --sq-depth NUM      SQ depth (default: 64)\n");
    printf("  --cq-depth NUM      CQ depth (default: 64)\n");
    printf("  --cpu CORE          CPU core to pin to (default: 7)\n");
    printf("  --priority NUM      Real-time priority 1-99 (default: 90)\n");
    printf("  --help              Show this help message\n");
    printf("\n");
    printf("Example:\n");
    printf("  sudo %s --device /dev/nvme0 --qid 1 \\\n", prog_name);
    printf("       --shadow 0x7f8a40000000 --cpu 7 --priority 90\n");
    printf("\n");
    printf("Setup isolated CPU:\n");
    printf("  1. Edit /etc/default/grub:\n");
    printf("       GRUB_CMDLINE_LINUX=\"isolcpus=7\"\n");
    printf("  2. sudo update-grub\n");
    printf("  3. sudo reboot\n");
    printf("\n");
}

int main(int argc, char** argv) {
    // Default configuration
    g_config.device_path = "/dev/nvme0";
    g_config.qid = 1;
    g_config.shadow_db_gpu = nullptr;
    g_config.sq_depth = 64;
    g_config.cq_depth = 64;
    g_config.cpu_core = 7;
    g_config.sched_priority = 90;

    // Parse command-line arguments
    static struct option long_options[] = {
        {"device", required_argument, 0, 'd'},
        {"qid", required_argument, 0, 'q'},
        {"shadow", required_argument, 0, 's'},
        {"sq-depth", required_argument, 0, 'S'},
        {"cq-depth", required_argument, 0, 'C'},
        {"cpu", required_argument, 0, 'c'},
        {"priority", required_argument, 0, 'p'},
        {"help", no_argument, 0, 'h'},
        {0, 0, 0, 0}
    };

    int opt;
    while ((opt = getopt_long(argc, argv, "d:q:s:S:C:c:p:h", long_options, nullptr)) != -1) {
        switch (opt) {
        case 'd':
            g_config.device_path = optarg;
            break;
        case 'q':
            g_config.qid = (uint16_t)atoi(optarg);
            break;
        case 's':
            g_config.shadow_db_gpu = (volatile uint32_t*)strtoull(optarg, nullptr, 16);
            break;
        case 'S':
            g_config.sq_depth = (uint16_t)atoi(optarg);
            break;
        case 'C':
            g_config.cq_depth = (uint16_t)atoi(optarg);
            break;
        case 'c':
            g_config.cpu_core = atoi(optarg);
            break;
        case 'p':
            g_config.sched_priority = atoi(optarg);
            if (g_config.sched_priority < 1 || g_config.sched_priority > 99) {
                fprintf(stderr, "Error: Priority must be 1-99\n");
                return 1;
            }
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
    if (!g_config.shadow_db_gpu) {
        fprintf(stderr, "Error: --shadow option is required\n");
        fprintf(stderr, "Get shadow buffer address from nvme_doorbell_mode_init()\n");
        print_usage(argv[0]);
        return 1;
    }

    // Check if running as root
    if (geteuid() != 0) {
        fprintf(stderr, "Error: Realtime daemon requires root privileges\n");
        fprintf(stderr, "Run with sudo or set CAP_SYS_NICE capability\n");
        return 1;
    }

    // Print configuration
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("Realtime Host DBC Daemon Starting\n");
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("  Device:           %s\n", g_config.device_path);
    printf("  Queue ID:         %u\n", g_config.qid);
    printf("  Shadow buffer:    %p\n", g_config.shadow_db_gpu);
    printf("  SQ depth:         %u\n", g_config.sq_depth);
    printf("  CQ depth:         %u\n", g_config.cq_depth);
    printf("  CPU core:         %d\n", g_config.cpu_core);
    printf("  RT priority:      %d (SCHED_FIFO)\n", g_config.sched_priority);
    printf("  Mode:             BUSY-WAIT (100%% CPU)\n");
    printf("═══════════════════════════════════════════════════════════════\n");

    // Register signal handlers
    signal(SIGINT, signal_handler);
    signal(SIGTERM, signal_handler);

    // Setup real-time environment
    printf("[RT-Daemon] Setting up real-time environment...\n");

    if (lock_memory() != 0) {
        fprintf(stderr, "[RT-Daemon] Failed to lock memory (continuing anyway)\n");
    }

    if (setup_realtime_scheduling(g_config.sched_priority) != 0) {
        fprintf(stderr, "[RT-Daemon] Failed to setup realtime scheduling\n");
        return 1;
    }

    if (pin_to_cpu(g_config.cpu_core) != 0) {
        fprintf(stderr, "[RT-Daemon] Failed to pin to CPU core\n");
        return 1;
    }

    // Map NVMe doorbells
    if (map_nvme_doorbells(&g_config) != 0) {
        fprintf(stderr, "Error: Failed to map NVMe doorbells\n");
        return 1;
    }

    // Start daemon
    g_running.store(true);
    printf("[RT-Daemon] Started successfully\n");
    printf("[RT-Daemon] Press Ctrl+C to stop\n\n");

    // Run busy-wait polling loop
    realtime_polling_loop(&g_config);

    // Cleanup
    printf("[RT-Daemon] Cleaning up...\n");
    unmap_nvme_doorbells(&g_config);

    // Print final statistics
    print_stats();

    printf("[RT-Daemon] Exited\n");
    return 0;
}
