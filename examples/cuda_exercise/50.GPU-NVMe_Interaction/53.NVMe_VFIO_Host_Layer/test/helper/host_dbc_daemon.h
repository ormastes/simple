/**
 * @file host_dbc_daemon.h
 * @brief Wrapper for HostDbcDaemonThread used by Mode 5 benchmarks
 *
 * Provides a simple interface to start/stop a host-side daemon that
 * polls shadow doorbell buffer and rings MMIO doorbells.
 */

#pragma once

#include <atomic>
#include <thread>
#include <chrono>
#include <cstdint>
#include "mapper/mapper_host.h"  // For NvmeDevice
#include "doorbell/nvme_doorbell.h"  // For DoorbellMode

/**
 * @brief Configuration for doorbell modes
 */
struct DoorbellModeConfig {
    DoorbellMode mode;
    uint16_t qid;
    uint16_t sq_depth;
    uint16_t cq_depth;
    uint32_t num_queues;
    uint32_t poll_interval_us;

    // Shadow doorbell arrays (indexed by 2*qid for SQ, 2*qid+1 for CQ)
    volatile uint32_t* shadow_doorbells;       // GPU device pointer
    volatile uint32_t* shadow_doorbells_host;  // Host pinned memory pointer

    // Individual shadow doorbell pointers (alternative API)
    volatile uint32_t* shadow_sq_tail;      // GPU writes here
    volatile uint32_t* shadow_cq_head;      // GPU writes here (CQ head)

    // MMIO doorbell pointers (for daemon to ring)
    volatile uint32_t* mmio_sq_doorbell;    // Daemon writes here
    volatile uint32_t* mmio_cq_doorbell;    // Daemon writes here (CQ)

    // Legacy names for compatibility
    volatile uint32_t* sq_db;               // Alias for mmio_sq_doorbell
    volatile uint32_t* cq_db;               // Alias for mmio_cq_doorbell
};

/**
 * @brief Initialize doorbell mode (stub - no-op for daemon mode)
 * @param fd Unused file descriptor (-1 for in-process daemon)
 * @param config Configuration to initialize
 * @return 0 on success
 */
inline int nvme_doorbell_mode_init(int fd, DoorbellModeConfig* config) {
    (void)fd;
    if (!config) return -1;
    return 0;  // No-op for daemon mode
}

/**
 * @brief Cleanup doorbell mode (stub - no-op for daemon mode)
 * @param config Configuration to cleanup
 */
inline void nvme_doorbell_mode_cleanup(DoorbellModeConfig* config) {
    (void)config;
    // No-op for daemon mode
}

/**
 * @brief Host DBC Daemon Thread wrapper for Mode 5 benchmarks
 *
 * Polls the shadow doorbell buffer and rings MMIO doorbells
 * when GPU updates the tail pointer.
 */
class HostDbcDaemonThread {
public:
    /**
     * @brief Construct daemon with doorbell config and NVMe device
     * @param config Doorbell mode configuration (contains shadow buffer pointers)
     * @param dev NVMe device handle
     * @param poll_interval_us Polling interval in microseconds (default 10us)
     */
    HostDbcDaemonThread(DoorbellModeConfig* config, NvmeDevice* dev,
                        uint32_t poll_interval_us = 10)
        : config_(config), dev_(dev), poll_interval_us_(poll_interval_us) {}

    ~HostDbcDaemonThread() {
        stop();
    }

    // Non-copyable, non-movable
    HostDbcDaemonThread(const HostDbcDaemonThread&) = delete;
    HostDbcDaemonThread& operator=(const HostDbcDaemonThread&) = delete;

    /**
     * @brief Start the daemon polling thread
     */
    void start() {
        if (running_.load(std::memory_order_acquire)) return;
        running_.store(true, std::memory_order_release);
        thread_ = std::thread(&HostDbcDaemonThread::run, this);
    }

    /**
     * @brief Stop the daemon thread
     */
    void stop() {
        running_.store(false, std::memory_order_release);
        if (thread_.joinable()) {
            thread_.join();
        }
    }

    /**
     * @brief Check if daemon is running
     */
    bool is_running() const {
        return running_.load(std::memory_order_acquire);
    }

    /**
     * @brief Get number of doorbell updates performed
     */
    uint64_t update_count() const {
        return update_count_.load(std::memory_order_relaxed);
    }

    /**
     * @brief Get number of doorbell writes (alias for update_count)
     */
    uint64_t get_doorbell_writes() const {
        return update_count_.load(std::memory_order_relaxed);
    }

private:
    void run() {
        if (!config_ || !dev_) return;

        // Get shadow doorbell buffer pointers from config
        volatile uint32_t* shadow_sq_tail = config_->shadow_sq_tail;
        volatile uint32_t* mmio_sq_doorbell = config_->mmio_sq_doorbell;

        if (!shadow_sq_tail || !mmio_sq_doorbell) return;

        uint32_t last_tail = 0;

        while (running_.load(std::memory_order_acquire)) {
            // Read shadow doorbell (GPU writes here)
            uint32_t current_tail = *shadow_sq_tail;

            // If tail changed, ring the MMIO doorbell
            if (current_tail != last_tail) {
                *mmio_sq_doorbell = current_tail;
                last_tail = current_tail;
                update_count_.fetch_add(1, std::memory_order_relaxed);
            }

            // Poll interval
            std::this_thread::sleep_for(std::chrono::microseconds(poll_interval_us_));
        }
    }

    DoorbellModeConfig* config_{nullptr};
    NvmeDevice* dev_{nullptr};
    uint32_t poll_interval_us_{10};
    std::thread thread_;
    std::atomic<bool> running_{false};
    std::atomic<uint64_t> update_count_{0};
};
