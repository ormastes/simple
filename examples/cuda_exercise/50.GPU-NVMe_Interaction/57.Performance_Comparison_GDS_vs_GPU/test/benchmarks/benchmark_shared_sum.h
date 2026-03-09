/**
 * @file benchmark_shared_sum.h
 * @brief Shared helpers for read-only 4KB + CUDA sum benchmarks (Modes 0-3).
 *
 * Each iteration:
 *   1) Issue a 4KB READ at the configured SLBA
 *   2) Move data to GPU (host copy unless true P2P is available)
 *   3) Launch the sum kernel (sum_4kb)
 *   4) Write the sum back to host memory (stores last sum only)
 *
 * Modes 0-3 run this loop on the host (kernel launched once per iteration).
 * Modes 4-6 use GPU-side looping and therefore have their own .cu helpers.
 */

#pragma once

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <stdexcept>
#include <string>
#include <vector>

#include <cuda_runtime.h>

#include "benchmark_constants.h"
#include "helper/benchmark_init_utils.h"
#include "kernels/sum_kernel.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "perf_timer.h"
#include "cuda_utils.h"
#include "helper/p2p_buffer_helper.h"

struct ModeDefinition {
    int mode_id;
    const char* name;
    bool pinned_host;
    bool gpu_buffer;
    bool gpu_command;
    bool dbc_daemon;
    bool gpu_cq;
    bool gpu_sq;
};

struct HostRunContext {
    NvmeDevice* dev{nullptr};
    HostPool* host_pool{nullptr};
    uint8_t* staging{nullptr};
    bool staging_pinned{false};
    uint8_t* gpu_buffer{nullptr};
    uint32_t* gpu_sum{nullptr};
    uint64_t gpu_buffer_prp{0};
    cudaStream_t stream{};
    size_t chunk_bytes{benchmark_constants::DEFAULT_BUFFER_SIZE_4KB};
    uint32_t lba_size{benchmark_constants::DEFAULT_LBA_SIZE};
    uint64_t start_lba{benchmark_constants::DEFAULT_START_LBA};
    uint64_t iterations{benchmark_constants::DEFAULT_ITERATIONS};
    P2PBufferHandle p2p_handle{};
    NvmeQueueStruct* gpu_queue_dev{nullptr};
};

inline uint64_t get_iterations_from_env() {
    const char* it_env = std::getenv("BENCH_ITERATIONS");
    if (!it_env) {
        it_env = std::getenv("BENCHMARK_ITERATIONS");
    }
    const uint64_t iterations = it_env ? std::strtoull(it_env, nullptr, 10) : 100000;
    return iterations == 0 ? 1 : iterations;
}

inline uint64_t get_start_lba_from_env() {
    const char* slba_env = std::getenv("NVME_SLBA");
    return slba_env ? std::strtoull(slba_env, nullptr, 10)
                    : benchmark_constants::DEFAULT_START_LBA;
}

inline void init_device_and_pool(const ModeDefinition& mode, HostRunContext& ctx) {
    const char* bdf = benchmark_constants::get_nvme_bdf_required();
    ctx.dev = nvme_open(bdf,
                        benchmark_constants::DEFAULT_SQ_DEPTH,
                        benchmark_constants::DEFAULT_CQ_DEPTH,
                        benchmark_constants::DEFAULT_BUFFER_SIZE_4KB);
    if (!ctx.dev) {
        throw std::runtime_error("nvme_open failed");
    }
    ctx.chunk_bytes = nvme_get_page_size(ctx.dev);
    ctx.lba_size = nvme_get_lba_size(ctx.dev);
    ctx.start_lba = get_start_lba_from_env();
    ctx.iterations = get_iterations_from_env();

    // Ensure known data pattern
    zero_lba0(ctx.dev, ctx.lba_size, ctx.start_lba);

    ctx.host_pool = host_pool_create(ctx.dev, 32);
    if (!ctx.host_pool) {
        nvme_close(ctx.dev);
        throw std::runtime_error("host_pool_create failed");
    }
}

inline void allocate_buffers(const ModeDefinition& mode, HostRunContext& ctx) {
    if (mode.gpu_command) {
        // GPU-initiated modes require P2P so NVMe can DMA directly into GPU memory
        ctx.p2p_handle = acquire_p2p_buffer(ctx.dev, ctx.chunk_bytes);
        if (ctx.p2p_handle.pool_buf) {
            ctx.gpu_buffer = static_cast<uint8_t*>(ctx.p2p_handle.pool_buf->addr);
            ctx.gpu_buffer_prp = ctx.p2p_handle.pool_buf->prp1;
        } else {
            // Fallback path (only if REQUIRE_P2P disabled)
            ctx.gpu_buffer = static_cast<uint8_t*>(ctx.p2p_handle.fallback_dev);
            ctx.gpu_buffer_prp = ctx.p2p_handle.host_buf ? ctx.p2p_handle.host_buf->prp1 : 0;
        }
        if (!ctx.gpu_buffer || ctx.gpu_buffer_prp == 0) {
            throw std::runtime_error("failed to acquire P2P-capable GPU buffer");
        }
        // No host staging needed for P2P path
        ctx.staging = nullptr;
    } else {
        if (mode.pinned_host) {
            CHECK_CUDA(cudaHostAlloc(reinterpret_cast<void**>(&ctx.staging),
                                     ctx.chunk_bytes, cudaHostAllocPortable));
            ctx.staging_pinned = true;
        } else {
            ctx.staging = static_cast<uint8_t*>(std::aligned_alloc(ctx.chunk_bytes, ctx.chunk_bytes));
            if (!ctx.staging) {
                throw std::runtime_error("failed to allocate pageable host buffer");
            }
            ctx.staging_pinned = false;
        }

        CHECK_CUDA(cudaMalloc(&ctx.gpu_buffer, ctx.chunk_bytes));
    }

    CHECK_CUDA(cudaMalloc(&ctx.gpu_sum, sizeof(uint32_t)));
    CHECK_CUDA(cudaStreamCreate(&ctx.stream));
}

inline void cleanup_context(HostRunContext& ctx) {
    if (ctx.gpu_queue_dev) cudaFree(ctx.gpu_queue_dev);
    if (ctx.stream) cudaStreamDestroy(ctx.stream);
    if (ctx.gpu_sum) cudaFree(ctx.gpu_sum);
    if (ctx.gpu_buffer && !ctx.p2p_handle.pool_buf && ctx.gpu_buffer_prp == 0) {
        // Only free plain cudaMalloc buffers; P2P pools are released below
        cudaFree(ctx.gpu_buffer);
    }
    if (ctx.p2p_handle.pool || ctx.p2p_handle.host_pool) {
        release_p2p_buffer(ctx.p2p_handle);
    }
    if (ctx.staging) {
        if (ctx.staging_pinned) {
            cudaFreeHost(ctx.staging);
        } else {
            std::free(ctx.staging);
        }
    }
    if (ctx.host_pool) host_pool_destroy(ctx.host_pool);
    if (ctx.dev) nvme_close(ctx.dev);
}

inline bool read_once(NvmeDevice* dev, HostPool* pool,
                      uint64_t lba, DmaBuf** out_dma) {
    DmaBuf* buf = host_pool_acquire(pool);
    if (!buf) return false;

    const uint16_t nlb = static_cast<uint16_t>((buf->bytes /
        nvme_get_lba_size(dev)) - 1);

    uint16_t cid = host_submit_runtime(
        CMD_READ,
        nullptr,
        nvme_get_iosq(dev),
        benchmark_constants::DEFAULT_NSID,
        lba,
        nvme_get_lba_size(dev),
        buf,
        buf->bytes);

    NvmeStatus st = host_poll_completion_runtime(
        ASYNC_TYPE_SYNC,
        nvme_get_iocq(dev),
        &cid,
        nullptr,
        benchmark_constants::POLL_TIMEOUT_US,
        nvme_get_iosq(dev));

    if (st.sc != 0) {
        host_pool_release(pool, buf);
        return false;
    }

    (void)nlb;  // keep compiler happy; nlb used only for clarity
    *out_dma = buf;
    return true;
}

inline int run_host_read_sum_benchmark(const ModeDefinition& mode) {
    HostRunContext ctx;
    try {
        init_device_and_pool(mode, ctx);
        allocate_buffers(mode, ctx);
    } catch (const std::exception& ex) {
        std::fprintf(stderr, "[Mode %d] Init failed: %s\n", mode.mode_id, ex.what());
        cleanup_context(ctx);
        return 1;
    }

    std::printf("[Mode %d] %s\n", mode.mode_id, mode.name);
    std::printf("  Iterations: %llu\n", (unsigned long long)ctx.iterations);
    std::printf("  Start LBA:  %llu\n", (unsigned long long)ctx.start_lba);
    std::printf("  Host buffer: %s\n", mode.pinned_host ? "Pinned" : "Pageable");
    std::printf("  GPU buffer:  %s\n", mode.gpu_buffer ? "Device" : "Host copy path");

    uint32_t last_sum = 0;
    bool warned_p2p = false;
    uint64_t current_lba = ctx.start_lba;  // Data-dependent LBA chain

    const auto bench_start = std::chrono::steady_clock::now();
    for (uint64_t i = 0; i < ctx.iterations; ++i) {
        DmaBuf* dma = nullptr;
        if (!read_once(ctx.dev, ctx.host_pool, current_lba, &dma)) {
            std::fprintf(stderr, "[Mode %d] READ failed at iter %llu\n",
                         mode.mode_id, (unsigned long long)i);
            cleanup_context(ctx);
            return 2;
        }

        // Stage data
        if (mode.pinned_host) {
            std::memcpy(ctx.staging, dma->addr, ctx.chunk_bytes);
        } else {
            std::memcpy(ctx.staging, dma->addr, ctx.chunk_bytes);
        }

        // Move to GPU (fallback copy if P2P unavailable)
        CHECK_CUDA(cudaMemcpyAsync(ctx.gpu_buffer, ctx.staging,
                                   ctx.chunk_bytes, cudaMemcpyHostToDevice,
                                   ctx.stream));
        CHECK_CUDA(cudaStreamSynchronize(ctx.stream));
        if (mode.gpu_buffer && !warned_p2p) {
            std::fprintf(stderr,
                         "[Mode %d] GPU buffer path: using host→GPU copy (P2P not wired here).\n",
                         mode.mode_id);
            warned_p2p = true;
        }

        // Sum kernel
        launch_sum_4kb(ctx.gpu_buffer, ctx.gpu_sum, ctx.stream);
        CHECK_CUDA(cudaStreamSynchronize(ctx.stream));
        CHECK_CUDA(cudaMemcpy(&last_sum, ctx.gpu_sum, sizeof(uint32_t),
                              cudaMemcpyDeviceToHost));

        current_lba = last_sum;

        // Save result back into staging so host can write/inspect (step 6)
        std::memcpy(ctx.staging, &last_sum, sizeof(uint32_t));

        host_pool_release(ctx.host_pool, dma);

        if ((i + 1) % 10000 == 0) {
            std::printf("  Iteration %llu / %llu (sum=%u)\n",
                        (unsigned long long)(i + 1),
                        (unsigned long long)ctx.iterations,
                        last_sum);
        }
    }
    const auto bench_end = std::chrono::steady_clock::now();

    const auto elapsed_us = std::chrono::duration_cast<std::chrono::microseconds>(
        bench_end - bench_start).count();
    const double elapsed_sec = static_cast<double>(elapsed_us) / 1e6;
    const double avg_latency_us = static_cast<double>(elapsed_us) / static_cast<double>(ctx.iterations);
    const double iops = static_cast<double>(ctx.iterations) / elapsed_sec;
    const double bandwidth_mbs = (iops * static_cast<double>(ctx.chunk_bytes)) / (1024.0 * 1024.0);

    std::printf("[Mode %d] Complete. Last sum=%u\n", mode.mode_id, last_sum);
    std::printf("[Mode %d] Duration: %.3f s, Average latency: %.2f us\n",
                mode.mode_id, elapsed_sec, avg_latency_us);
    std::printf("[Mode %d] IOPS: %.0f ops/sec, Bandwidth: %.2f MB/s\n",
                mode.mode_id, iops, bandwidth_mbs);
    cleanup_context(ctx);
    return 0;
}
