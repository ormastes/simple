/**
 * @file host_io_test_utils.h
 * @brief Reusable helpers for NVMe host I/O system tests
 *
 * Provides small RAII wrappers and submission helpers so the system
 * tests can stay focused on intent instead of repetitive plumbing.
 */

#pragma once

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <vector>

#include "doorbell/nvme_doorbell.h"
#include "helper/system_test_config.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "nvme_types.h"  // For PollResult enum

namespace nvme_test {

/**
 * @brief Lightweight context bundling NVMe queues and test config
 */
struct IoContext {
    NvmeDevice* device{nullptr};
    Queue* submission_queue{nullptr};
    Queue* completion_queue{nullptr};
    const HostTestConfig* config{nullptr};

    bool valid() const {
        return device && submission_queue && completion_queue && config;
    }
};

/**
 * @brief Result of a single NVMe command submission
 */
struct IoCompletion {
    uint16_t submitted_cid{std::numeric_limits<uint16_t>::max()};
    uint16_t completed_cid{std::numeric_limits<uint16_t>::max()};
    NvmeStatus status{};
    PollResult poll{POLL_NOT_READY};

    bool is_success() const {
        return submitted_cid != std::numeric_limits<uint16_t>::max() &&
               submitted_cid == completed_cid &&
               poll == POLL_READY &&
               !status.is_error();
    }
};

/**
 * @brief RAII wrapper around HostPool*
 */
class HostPoolGuard {
public:
    HostPoolGuard() = default;

    HostPoolGuard(NvmeDevice* dev, uint16_t count) {
        reset(dev, count);
    }

    ~HostPoolGuard() {
        reset();
    }

    HostPoolGuard(const HostPoolGuard&) = delete;
    HostPoolGuard& operator=(const HostPoolGuard&) = delete;

    HostPoolGuard(HostPoolGuard&& other) noexcept {
        pool_ = other.pool_;
        other.pool_ = nullptr;
    }

    HostPoolGuard& operator=(HostPoolGuard&& other) noexcept {
        if (this != &other) {
            reset();
            pool_ = other.pool_;
            other.pool_ = nullptr;
        }
        return *this;
    }

    void reset(NvmeDevice* dev = nullptr, uint16_t count = 0) {
        if (pool_) {
            host_pool_destroy(pool_);
            pool_ = nullptr;
        }
        if (dev && count) {
            pool_ = host_pool_create(dev, count);
        }
    }

    bool valid() const { return pool_ != nullptr; }

    HostPool* get() const { return pool_; }

    uint16_t capacity() const { return pool_ ? pool_->cap : 0; }
    size_t buffer_size() const { return pool_ ? pool_->buf_size : 0; }
    uint16_t in_use() const { return pool_ ? pool_->in_use : 0; }

    DmaBuf* acquire() { return pool_ ? host_pool_acquire(pool_) : nullptr; }
    void release(DmaBuf* buf) {
        if (pool_ && buf) {
            host_pool_release(pool_, buf);
        }
    }

private:
    HostPool* pool_{nullptr};
};

/**
 * @brief Scoped DMA buffer borrowed from a HostPoolGuard
 */
class ScopedDmaBuf {
public:
    explicit ScopedDmaBuf(HostPoolGuard& pool) : pool_(&pool), buf_(pool.acquire()) {}
    ~ScopedDmaBuf() { reset(); }

    ScopedDmaBuf(const ScopedDmaBuf&) = delete;
    ScopedDmaBuf& operator=(const ScopedDmaBuf&) = delete;

    ScopedDmaBuf(ScopedDmaBuf&& other) noexcept {
        pool_ = other.pool_;
        buf_ = other.buf_;
        other.pool_ = nullptr;
        other.buf_ = nullptr;
    }

    ScopedDmaBuf& operator=(ScopedDmaBuf&& other) noexcept {
        if (this != &other) {
            reset();
            pool_ = other.pool_;
            buf_ = other.buf_;
            other.pool_ = nullptr;
            other.buf_ = nullptr;
        }
        return *this;
    }

    DmaBuf* get() const { return buf_; }
    DmaBuf* operator->() const { return buf_; }

    void reset() {
        if (pool_ && buf_) {
            pool_->release(buf_);
        }
        pool_ = nullptr;
        buf_ = nullptr;
    }

private:
    HostPoolGuard* pool_{nullptr};
    DmaBuf* buf_{nullptr};
};

inline void clear_buffer(DmaBuf* buf, size_t bytes) {
    if (buf && buf->addr && bytes) {
        std::memset(buf->addr, 0, bytes);
    }
}

inline bool buffer_has_nonzero(const DmaBuf* buf, size_t bytes) {
    if (!buf || !buf->addr) {
        return false;
    }
    const auto* data = static_cast<const uint8_t*>(buf->addr);
    for (size_t i = 0; i < bytes; ++i) {
        if (data[i] != 0) {
            return true;
        }
    }
    return false;
}

inline std::vector<DmaBuf*> acquire_buffers(HostPoolGuard& pool, uint16_t count) {
    std::vector<DmaBuf*> buffers;
    buffers.reserve(count);
    for (uint16_t i = 0; i < count; ++i) {
        if (auto* buf = pool.acquire()) {
            buffers.push_back(buf);
        }
    }
    return buffers;
}

inline void release_buffers(HostPoolGuard& pool, std::vector<DmaBuf*>& buffers) {
    for (auto* buf : buffers) {
        pool.release(buf);
    }
    buffers.clear();
}

template <CommandType cmd, typename DoorbellT = ImmediateDoorbell>
IoCompletion submit_io(const IoContext& ctx, DmaBuf* buf, uint64_t slba,
                       size_t bytes, uint64_t timeout_us = 5'000'000) {
    IoCompletion result;
    if (!ctx.valid() || !buf) {
        return result;
    }

    result.submitted_cid = host_submit<cmd, DoorbellT>(
        ctx.submission_queue, ctx.config->nsid, slba, ctx.config->lba_size, buf, bytes);

    if (result.submitted_cid == NVME_CID_QUEUE_FULL) {
        result.poll = POLL_ERROR;  // Queue full is an error condition
        return result;
    }

    uint16_t completed_cid = 0;
    result.status = host_poll_completion<ASYNC_TYPE_SYNC>(
        ctx.completion_queue, &completed_cid, &result.poll, timeout_us, ctx.submission_queue);
    result.completed_cid = completed_cid;
    return result;
}

template <typename DoorbellT = ImmediateDoorbell>
inline IoCompletion submit_read(const IoContext& ctx, DmaBuf* buf, uint64_t slba,
                                size_t bytes, uint64_t timeout_us = 5'000'000) {
    return submit_io<CMD_READ, DoorbellT>(ctx, buf, slba, bytes, timeout_us);
}

template <typename DoorbellT = ImmediateDoorbell>
inline IoCompletion submit_write(const IoContext& ctx, DmaBuf* buf, uint64_t slba,
                                 size_t bytes, uint64_t timeout_us = 5'000'000) {
    return submit_io<CMD_WRITE, DoorbellT>(ctx, buf, slba, bytes, timeout_us);
}

}  // namespace nvme_test
