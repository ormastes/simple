/**
 * @file benchmark_init_utils.h
 * @brief Shared helpers to initialize NVMe media for benchmarks.
 *
 * Ensures a known pattern (zeros) is written to LBA 0 before benchmarks run,
 * so reads from the start of the device have deterministic data.
 */
#pragma once

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"

/**
 * @brief Initialize a test LBA with self-referential pattern before benchmarks run.
 *
 * Uses the test area LBA (from NVME_SLBA env var) to avoid writing to
 * protected areas like LBA 0 (boot sector).
 *
 * For data-dependent addressing benchmarks (Modes 4-6), the data is written
 * such that when the GPU computes sum(4KB), the result equals the start_lba.
 * This creates a circular read pattern that stays within the safe test area.
 *
 * Pattern: First uint32_t = start_lba, rest = 0
 * Result: sum = start_lba + 0 + 0 + ... = start_lba
 *
 * @param dev NVMe device handle
 * @param lba_size_bytes LBA size in bytes
 * @param slba Starting LBA to initialize (defaults to NVME_SLBA env var or 2000000)
 */
inline void zero_lba0(NvmeDevice* dev, uint32_t lba_size_bytes, uint64_t slba = 0) {
    if (!dev) return;

    // Use the test area LBA instead of the potentially protected LBA 0
    if (slba == 0) {
        const char* slba_env = std::getenv("NVME_SLBA");
        slba = slba_env ? std::strtoull(slba_env, nullptr, 10) : 2000000;
    }

    // Use a small host DMA buffer via the pool helpers
    HostPool* pool = host_pool_create(dev, 1);
    if (!pool) {
        throw std::runtime_error("zero_lba0: failed to create host pool");
    }

    DmaBuf* buf = host_pool_acquire(pool);
    if (!buf || !buf->addr || buf->bytes == 0) {
        host_pool_destroy(pool);
        throw std::runtime_error("zero_lba0: failed to acquire DMA buffer");
    }

    // Write self-referential pattern: first uint32_t = slba, rest = 0
    // When GPU sums 1024 uint32_t elements, result = slba + 0 + ... = slba
    // This creates a circular read loop that stays in the safe test area
    const size_t bytes = buf->bytes >= 4096 ? 4096 : lba_size_bytes;
    std::memset(buf->addr, 0, bytes);

    // Write start_lba as first uint32_t (truncated to 32-bit for sum compatibility)
    uint32_t* data = static_cast<uint32_t*>(buf->addr);
    data[0] = static_cast<uint32_t>(slba);

    uint16_t cid = host_submit_runtime(CMD_WRITE,
                                       /*doorbell*/ nullptr,
                                       nvme_get_iosq(dev),
                                       /*nsid*/ 1,
                                       slba,  // Use test area LBA instead of 0
                                       lba_size_bytes,
                                       buf,
                                       bytes);

    NvmeStatus st = host_poll_completion_runtime(ASYNC_TYPE_SYNC,
                                                 nvme_get_iocq(dev),
                                                 &cid,
                                                 nullptr,
                                                 /*timeout_us*/ 0,
                                                 nvme_get_iosq(dev));
    if (st.sc != 0 || st.sct != 0) {
        host_pool_release(pool, buf);
        host_pool_destroy(pool);
        throw std::runtime_error("zero_lba0: NVMe write completion error");
    }

    host_pool_release(pool, buf);
    host_pool_destroy(pool);
}
