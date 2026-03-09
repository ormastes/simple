/**
 * @file host_submission.cpp
 * @brief Host-side implementation for host_submission
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

// host_submission.cpp - Host-based 4KB read submission
#include <chrono>
#include <cstring>
#include <string>
#include <optional>
#include <stdexcept>
#include "common/benchmark_base.h"
#include "common/timer.h"
#include "mapper/mapper_host.h"
#include "io/host_io_host_mem.h"
#include "memory/host_memory_buffer.h"
#include "device/device_detector.h"
#include <cuda_runtime.h>

/**
 * Host-based submission class for 4KB reads
 *
 * This implementation uses the CPU to submit NVMe commands and optionally
 * transfers data to GPU memory upon completion.
 */
class HostSubmission {
private:
    NvmeDevice* nvme_device_;
    Queue* iosq_;
    Queue* iocq_;
    HostPool* host_pool_;
    DmaBuf* dma_buf_;
    void* gpu_buffer_;
    cudaStream_t stream_;
    bool use_gpu_target_;
    uint32_t lba_size_;

public:
    HostSubmission(bool use_gpu_target = false)
        : nvme_device_(nullptr),
          iosq_(nullptr),
          iocq_(nullptr),
          host_pool_(nullptr),
          dma_buf_(nullptr),
          gpu_buffer_(nullptr),
          stream_(nullptr),
          use_gpu_target_(use_gpu_target),
          lba_size_(512) {

        // Select NVMe device: env NVME_BDF first, otherwise first safe NVMe
        std::string bdf = "/dev/nvme0";
        if (const char* env_bdf = std::getenv("NVME_BDF")) {
            bdf = env_bdf;
        } else {
            SystemFeatures features = SystemFeatures::detect_all();
            for (const auto& nvme : features.nvme_devs) {
                if (!nvme.is_available() || nvme.is_os_live()) continue;
                bdf = nvme.get_pci_bus_id();
                break;
            }
        }

        // Open NVMe device and queues
        nvme_device_ = nvme_open(bdf.c_str(), /*admin_qd=*/64, /*io_qd=*/256, /*item_size_bytes=*/4096);
        if (!nvme_device_) {
            throw std::runtime_error("Failed to open NVMe device at " + bdf);
        }
        lba_size_ = nvme_get_lba_size(nvme_device_);

        iosq_ = nvme_get_iosq(nvme_device_);
        iocq_ = nvme_get_iocq(nvme_device_);
        if (!iosq_ || !iocq_) {
            throw std::runtime_error("Failed to get IO queues");
        }

        // Allocate host DMA buffer from pool
        host_pool_ = host_pool_create(nvme_device_, /*count=*/4);
        if (!host_pool_) {
            throw std::runtime_error("host_pool_create failed");
        }
        dma_buf_ = host_pool_acquire(host_pool_);
        if (!dma_buf_) {
            throw std::runtime_error("host_pool_acquire failed");
        }
        if (dma_buf_->bytes < 4096) {
            throw std::runtime_error("DMA buffer too small for 4KB transfer");
        }

        if (use_gpu_target_) {
            cudaError_t err = cudaMalloc(&gpu_buffer_, 4096);
            if (err != cudaSuccess) {
                throw std::runtime_error("cudaMalloc failed for GPU target buffer");
            }
            cudaStreamCreate(&stream_);
        }
    }

    ~HostSubmission() {
        if (dma_buf_ && host_pool_) {
            host_pool_release(host_pool_, dma_buf_);
        }
        if (host_pool_) {
            host_pool_destroy(host_pool_);
        }
        if (use_gpu_target_) {
            if (gpu_buffer_) cudaFree(gpu_buffer_);
            if (stream_) cudaStreamDestroy(stream_);
        }
        if (nvme_device_) {
            nvme_close(nvme_device_);
        }
    }

    /**
     * Synchronous 4KB read with detailed timing
     */
    ReadResult read_4kb_sync(uint64_t lba) {
        ReadResult result;
        Timer total_timer, component_timer;

        total_timer.start();

        // 1. Build + submit NVMe read command to host queue
        component_timer.start();
        uint16_t cid = host_submit_runtime(CommandType::READ,
                                           /*doorbell=*/nullptr,
                                           iosq_,
                                           /*nsid=*/1,
                                           lba,
                                           lba_size_,
                                           dma_buf_,
                                           /*bytes=*/4096);
        component_timer.stop();
        result.command_build_ns = component_timer.elapsed_ns();
        result.submission_ns = component_timer.elapsed_ns();  // merged for simplicity

        // 2. Doorbell is part of submit_runtime; keep as zero since cost included above
        result.doorbell_ns = 0;

        // 4. Poll completion
        component_timer.start();
        NvmeStatus st = host_poll_completion_runtime(AsyncType::SYNC, iocq_, &cid, nullptr, /*timeout_us=*/0, iosq_);
        component_timer.stop();
        result.completion_ns = component_timer.elapsed_ns();
        result.success = (st.sc == 0 && st.sct == 0);

        // 5. Optional GPU copy
        if (use_gpu_target_ && gpu_buffer_) {
            component_timer.start();
            cudaMemcpyAsync(gpu_buffer_, dma_buf_->addr, 4096,
                            cudaMemcpyHostToDevice, stream_);
            cudaStreamSynchronize(stream_);
            component_timer.stop();
            result.copy_to_gpu_ns = component_timer.elapsed_ns();
        }

        total_timer.stop();
        result.total_ns = total_timer.elapsed_ns();

        return result;
    }

    /**
     * Batch submission for throughput testing
     */
    void read_4kb_batch(const std::vector<uint64_t>& lbas,
                        std::vector<ReadResult>& results) {
        for (size_t i = 0; i < lbas.size(); ++i) {
            results[i] = read_4kb_sync(lbas[i]);
        }
    }
};

// Placeholder for testing
void* test_host_submission() {
    HostSubmission submitter(false);

    // Test single read
    ReadResult result = submitter.read_4kb_sync(0);

    return nullptr;
}
