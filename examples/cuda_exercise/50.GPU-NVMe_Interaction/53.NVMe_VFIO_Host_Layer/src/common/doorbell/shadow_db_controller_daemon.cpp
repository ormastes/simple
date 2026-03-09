/**
 * @file shadow_db_controller_daemon.cpp
 */

#include "shadow_db_controller_daemon.h"

#include <atomic>
#include <thread>

namespace nvme {

namespace {
// Helper to write with ordering for MMIO visibility
inline void mmio_write(volatile uint32_t* db, uint32_t value) {
    std::atomic_thread_fence(std::memory_order_release);
    *db = value;
    std::atomic_thread_fence(std::memory_order_seq_cst);
}
}  // namespace

ShadowDbControllerDaemon::ShadowDbControllerDaemon(
    ShadowDoorbellBuffer* shadow_buffer,
    volatile uint32_t* sq_db,
    volatile uint32_t* cq_db,
    uint16_t qid,
    uint32_t doorbell_stride_bytes,
    std::chrono::microseconds poll_interval)
    : shadow_buffer_(shadow_buffer)
    , sq_db_(sq_db)
    , cq_db_(cq_db)
    , qid_(qid)
    , stride_bytes_(doorbell_stride_bytes)
    , poll_interval_(poll_interval) {
    if (shadow_buffer_ && shadow_buffer_->host_ptr && stride_bytes_ > 0) {
        auto* base = reinterpret_cast<volatile uint8_t*>(shadow_buffer_->host_ptr);
        last_sq_ = *reinterpret_cast<volatile uint32_t*>(const_cast<uint8_t*>(base) +
                                                        static_cast<size_t>(2 * qid_) * stride_bytes_);
        last_cq_ = *reinterpret_cast<volatile uint32_t*>(const_cast<uint8_t*>(base) +
                                                        static_cast<size_t>(2 * qid_ + 1) * stride_bytes_);
    }
}

ShadowDbControllerDaemon::~ShadowDbControllerDaemon() {
    stop();
}

void ShadowDbControllerDaemon::start() {
    if (running_.load(std::memory_order_acquire) || !shadow_buffer_ || !shadow_buffer_->host_ptr ||
        !sq_db_ || !cq_db_ || stride_bytes_ == 0) {
        return;
    }

    running_.store(true, std::memory_order_release);
    thread_ = std::thread(&ShadowDbControllerDaemon::run, this);
}

void ShadowDbControllerDaemon::stop() {
    if (!running_.load(std::memory_order_acquire)) {
        return;
    }

    running_.store(false, std::memory_order_release);
    if (thread_.joinable()) {
        thread_.join();
    }
}

void ShadowDbControllerDaemon::run() {
    auto* base = reinterpret_cast<volatile uint8_t*>(shadow_buffer_->host_ptr);
    const size_t sq_offset = static_cast<size_t>(2 * qid_) * stride_bytes_;
    const size_t cq_offset = static_cast<size_t>(2 * qid_ + 1) * stride_bytes_;

    while (running_.load(std::memory_order_acquire)) {
        const uint32_t sq_val = *reinterpret_cast<volatile uint32_t*>(const_cast<uint8_t*>(base) + sq_offset);
        const uint32_t cq_val = *reinterpret_cast<volatile uint32_t*>(const_cast<uint8_t*>(base) + cq_offset);

        if (sq_val != last_sq_) {
            mmio_write(sq_db_, sq_val);
            last_sq_ = sq_val;
            update_count_.fetch_add(1, std::memory_order_relaxed);
        }
        if (cq_val != last_cq_) {
            mmio_write(cq_db_, cq_val);
            last_cq_ = cq_val;
            update_count_.fetch_add(1, std::memory_order_relaxed);
        }

        std::this_thread::sleep_for(poll_interval_);
    }
}

}  // namespace nvme
