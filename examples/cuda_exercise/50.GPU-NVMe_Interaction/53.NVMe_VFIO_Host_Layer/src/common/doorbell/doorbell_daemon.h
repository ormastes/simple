/**
 * @file doorbell_daemon.h
 * @brief Host-side daemon that polls SQ tail and rings NVMe MMIO doorbells
 */

#pragma once

#include <atomic>
#include <chrono>
#include <cstdint>
#include <thread>

#include "../host/mapper/mapper_host.h"  // For Queue definition

namespace nvme {

/**
 * @brief Doorbell daemon for host-initiated doorbell ringing
 */
class DoorbellDaemon {
public:
    /**
     * @brief Construct doorbell daemon
     * @param iosq Submission queue to monitor
     * @param poll_interval Polling interval
     */
    DoorbellDaemon(Queue* iosq,
                   std::chrono::microseconds poll_interval = std::chrono::microseconds(10));

    /**
     * @brief Destructor
     */
    ~DoorbellDaemon();

    // Disable copy/move
    DoorbellDaemon(const DoorbellDaemon&) = delete;
    DoorbellDaemon& operator=(const DoorbellDaemon&) = delete;
    DoorbellDaemon(DoorbellDaemon&&) = delete;
    DoorbellDaemon& operator=(DoorbellDaemon&&) = delete;

    /**
     * @brief Start the daemon thread
     */
    void start();

    /**
     * @brief Stop the daemon thread
     */
    void stop();

    /**
     * @brief Get the number of doorbell rings performed
     * @return Total ring count
     */
    uint64_t ring_count() const {
        return ring_count_.load(std::memory_order_relaxed);
    }

    /**
     * @brief Wait for a specific number of doorbell rings
     * @param target_count Target count
     * @param timeout Max time
     * @return true if reached, false if timeout
     */
    bool wait_for_ring_count(uint64_t target_count,
                            std::chrono::milliseconds timeout);

    /**
     * @brief Check if daemon is running
     * @return true if active
     */
    bool is_running() const {
        return running_.load(std::memory_order_acquire);
    }

    /**
     * @brief Get polling interval
     * @return Interval in microseconds
     */
    std::chrono::microseconds get_poll_interval() const {
        return poll_interval_;
    }

private:
    void run();

    Queue* iosq_{nullptr};                      ///< Submission queue to monitor
    std::chrono::microseconds poll_interval_;   ///< Polling interval
    std::thread thread_;                        ///< Daemon thread
    std::atomic<bool> running_{false};          ///< Running state flag
    std::atomic<uint64_t> ring_count_{0};       ///< Total doorbell rings
    uint16_t tail_shadow_{0};                   ///< Cached tail pointer value
};

}  // namespace nvme