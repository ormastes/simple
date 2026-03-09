/**
 * @file shadow_db_controller_daemon.h
 * @brief Host-side helper that mirrors shadow doorbell writes into MMIO doorbells
 *
 * Used for hardware that advertises DBC but does not autonomously poll the
 * shadow buffer (e.g., firmware hiding bit 8) or for emulated controllers
 * where we want a software thread to observe shadow buffer updates and ring
 * the real doorbells.
 */

#pragma once

#include <atomic>
#include <chrono>
#include <cstdint>
#include <thread>
#include <vector>

#include "dbc_setup.h"  // For ShadowDoorbellBuffer

namespace nvme {

/**
 * @brief Mirror shadow doorbell buffer writes into hardware doorbells.
 *
 * The daemon polls the shadow buffer for a specific queue ID and, when a new
 * value is observed, writes it to the provided MMIO SQ/CQ doorbell
 * registers. This is intentionally lightweight so it can be used in test
 * harnesses as a stopgap when true hardware DBC polling is unavailable.
 */
class ShadowDbControllerDaemon {
public:
    ShadowDbControllerDaemon(ShadowDoorbellBuffer* shadow_buffer,
                             volatile uint32_t* sq_db,
                             volatile uint32_t* cq_db,
                             uint16_t qid,
                             uint32_t doorbell_stride_bytes,
                             std::chrono::microseconds poll_interval =
                                 std::chrono::microseconds(10));

    ~ShadowDbControllerDaemon();

    ShadowDbControllerDaemon(const ShadowDbControllerDaemon&) = delete;
    ShadowDbControllerDaemon& operator=(const ShadowDbControllerDaemon&) = delete;
    ShadowDbControllerDaemon(ShadowDbControllerDaemon&&) = delete;
    ShadowDbControllerDaemon& operator=(ShadowDbControllerDaemon&&) = delete;

    /** Start polling thread. No-op if already running. */
    void start();

    /** Stop polling thread and join. Safe to call multiple times. */
    void stop();

    bool is_running() const { return running_.load(std::memory_order_acquire); }

    uint64_t update_count() const { return update_count_.load(std::memory_order_relaxed); }

private:
    void run();

    ShadowDoorbellBuffer* shadow_buffer_{nullptr};
    volatile uint32_t* sq_db_{nullptr};
    volatile uint32_t* cq_db_{nullptr};
    uint16_t qid_{0};
    uint32_t stride_bytes_{0};
    std::chrono::microseconds poll_interval_;
    std::thread thread_;
    std::atomic<bool> running_{false};
    std::atomic<uint64_t> update_count_{0};
    uint32_t last_sq_{0};
    uint32_t last_cq_{0};
};

}  // namespace nvme

