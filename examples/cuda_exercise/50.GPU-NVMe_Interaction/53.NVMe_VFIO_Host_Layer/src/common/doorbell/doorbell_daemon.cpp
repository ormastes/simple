/**
 * @file doorbell_daemon.cpp
 * @brief Implementation of the doorbell daemon
 *
 * @author Yoon, Jonghyun
 * @date 2025-11-20
 */

#include "doorbell_daemon.h"

#include <atomic>
#include <chrono>
#include <thread>

namespace nvme {

namespace {

/**
 * @brief Write to MMIO doorbell register with proper memory barriers
 * @param db Doorbell register pointer
 * @param value Value to write (typically queue tail pointer)
 */
inline void mmio_write(volatile uint32_t* db, uint16_t value) {
    std::atomic_thread_fence(std::memory_order_release);
    *db = value;
    std::atomic_thread_fence(std::memory_order_seq_cst);
}

}  // anonymous namespace

DoorbellDaemon::DoorbellDaemon(Queue* iosq,
                               std::chrono::microseconds poll_interval)
    : iosq_(iosq), poll_interval_(poll_interval) {
    if (iosq_) {
        tail_shadow_ = iosq_->tail;
    }
}

DoorbellDaemon::~DoorbellDaemon() {
    stop();
}

void DoorbellDaemon::start() {
    if (!iosq_ || !iosq_->db || running_.load()) {
        return;  // Already running or invalid queue
    }
    running_.store(true);
    thread_ = std::thread(&DoorbellDaemon::run, this);
}

void DoorbellDaemon::stop() {
    if (!running_.load()) {
        return;  // Not running
    }
    running_.store(false);
    if (thread_.joinable()) {
        thread_.join();
    }
}

bool DoorbellDaemon::wait_for_ring_count(uint64_t target_count,
                                         std::chrono::milliseconds timeout) {
    auto deadline = std::chrono::steady_clock::now() + timeout;
    while (std::chrono::steady_clock::now() < deadline) {
        if (ring_count_.load(std::memory_order_acquire) >= target_count) {
            return true;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(1));
    }
    return ring_count_.load(std::memory_order_acquire) >= target_count;
}

void DoorbellDaemon::run() {
    while (running_.load(std::memory_order_acquire)) {
        uint16_t current_tail = iosq_->tail;
        if (current_tail != tail_shadow_) {
            // New commands detected - ring the doorbell
            mmio_write(iosq_->db, current_tail);
            tail_shadow_ = current_tail;
            ring_count_.fetch_add(1, std::memory_order_relaxed);
        }
        std::this_thread::sleep_for(poll_interval_);
    }
}

}  // namespace nvme