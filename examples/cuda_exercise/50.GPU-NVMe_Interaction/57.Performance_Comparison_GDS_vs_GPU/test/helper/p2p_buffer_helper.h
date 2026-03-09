/**
 * @file p2p_buffer_helper.h
 * @brief Utility to acquire a GPU buffer with P2P IOVA or fallback to pinned bounce.
 *
 * This centralizes P2P vs. fallback logic and logs the selected path.
 */
#pragma once

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include "benchmarks/benchmark_constants.h"
#include "mapper/mapper_host.h"
#include "memory/cuda_host_memory_buffer.h"
#include "memory/cuda_gpu_memory_buffer.h"

struct P2PBufferHandle {
    CudaGpuPool* pool{nullptr};
    DmaBuf* pool_buf{nullptr};  // using_p2p flag is stored on DmaBuf

    CudaHostPool* host_pool{nullptr};
    DmaBuf* host_buf{nullptr};

    // Fallback (no P2P) uses host_buf and its device_alias
    void* fallback_dev{nullptr};
    size_t bytes{0};
};

/**
 * @brief Acquire a GPU buffer with P2P mapping if available, else host bounce.
 *
 * @param dev NVMe device (for VFIO mapping)
 * @param bytes buffer size
 * @return P2PBuffer with chosen path; exits if REQUIRE_P2P=1 and P2P unavailable
 */
inline P2PBufferHandle acquire_p2p_buffer(NvmeDevice* dev, size_t bytes) {
    P2PBufferHandle out{};
    out.bytes = bytes;

    // Try GPU P2P pool first
    out.pool = cuda_gpu_pool_create(dev, bytes, 1);
    if (out.pool) {
        out.pool_buf = cuda_gpu_pool_acquire(out.pool);
        if (out.pool_buf && out.pool_buf->prp1 != 0) {
            std::fprintf(stderr, "[P2PBuffer] Using GPU P2P mapping: dev_ptr=%p, IOVA=0x%lx\n",
                         out.pool_buf->addr, out.pool_buf->prp1);
            return out;
        }
        // Release pool if mapping failed
        if (out.pool_buf) {
            cuda_gpu_pool_release(out.pool, out.pool_buf);
            out.pool_buf = nullptr;
        }
        cuda_gpu_pool_destroy(out.pool);
        out.pool = nullptr;
    }

    if (benchmark_constants::require_p2p_enabled()) {
        std::fprintf(stderr, "[P2PBuffer] REQUIRE_P2P=1 set but P2P mapping unavailable\n");
        std::exit(1);
    }

    // Fallback: pinned host bounce buffer via CUDA host pool + IOVA
    out.host_pool = cuda_host_pool_create_ex(dev, bytes, 1, PoolAllocMode::HOST_WITH_DEVICE_SHADOW);
    if (!out.host_pool) {
        std::fprintf(stderr, "[P2PBuffer] cuda_host_pool_create failed for fallback buffer\n");
        std::exit(1);
    }
    out.host_buf = cuda_host_pool_acquire(out.host_pool);
    if (!out.host_buf || out.host_buf->prp1 == 0) {
        std::fprintf(stderr, "[P2PBuffer] cuda_host_pool_acquire failed for fallback buffer\n");
        cuda_host_pool_destroy(out.host_pool);
        std::exit(1);
    }
    std::fprintf(stderr, "[P2PBuffer] Using pinned host bounce buffer, IOVA=0x%lx\n", out.host_buf->prp1);

    // Allocate GPU buffer for computation when using bounce path
    out.fallback_dev = out.host_buf->device_alias;
    if (!out.fallback_dev) {
        std::fprintf(stderr, "[P2PBuffer] host buffer missing device shadow\n");
        cuda_host_pool_release(out.host_pool, out.host_buf);
        cuda_host_pool_destroy(out.host_pool);
        std::exit(1);
    }

    return out;
}

inline void release_p2p_buffer(P2PBufferHandle& buf) {
    if (buf.pool) {
        if (buf.pool_buf) {
            cuda_gpu_pool_release(buf.pool, buf.pool_buf);
        }
        cuda_gpu_pool_destroy(buf.pool);
    }
    if (buf.host_pool) {
        if (buf.host_buf) {
            cuda_host_pool_release(buf.host_pool, buf.host_buf);
        }
        cuda_host_pool_destroy(buf.host_pool);
    }
    buf = {};
}
