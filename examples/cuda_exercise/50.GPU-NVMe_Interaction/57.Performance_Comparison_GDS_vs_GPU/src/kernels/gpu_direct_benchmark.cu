/**
 * @file gpu_direct_benchmark.cu
 * @brief CUDA kernel implementation for gpu_direct_benchmark
 *
 * @author Yoon, Jonghyun
 * @date 2025-10-25
 */

// gpu_direct_benchmark.cu - GPU Direct Command Submission benchmark
#include <cuda_runtime.h>
#include <cstdio>
#include <cstdlib>
#include "mapper/mapper_host.h"
#include "mapper/mapper_gpu.h"

/**
 * GPU kernel that submits NVMe read command and sums the result
 *
 * This demonstrates GPU Direct Command submission where the GPU itself
 * submits NVMe commands without host involvement.
 */
__global__ void gpu_submit_read_and_sum_kernel(
    Queue* iosq,
    Queue* iocq,
    uint64_t lba,
    void* gpu_buffer,
    uint64_t buffer_iova,
    uint32_t* result,
    uint64_t* timing_ns
) {
    if (threadIdx.x != 0 || blockIdx.x != 0) return;  // Only thread 0 executes

    // Start timing
    clock_t start = clock64();

    // Build NVMe read command
    NvmeCmd cmd{};
    cmd.opc = OPC_NVM_READ;
    cmd.cid = static_cast<uint16_t>(blockIdx.x);
    cmd.nsid = 1;

    // Set PRP for 4KB transfer
    cmd.prp1 = buffer_iova;
    cmd.prp2 = 0;  // 4KB fits in single page

    // LBA and block count
    cmd.cdw10 = static_cast<uint32_t>(lba & 0xFFFFFFFF);
    cmd.cdw11 = static_cast<uint32_t>(lba >> 32);
    cmd.cdw12 = 0;  // 1 block (0-based count)

    // Submit to SQ
    NvmeCmd* sq_entry = reinterpret_cast<NvmeCmd*>(
        static_cast<char*>(iosq->vaddr) +
        (iosq->tail * iosq->entry_size)
    );
    *sq_entry = cmd;
    __threadfence_system();  // Ensure command is visible

    // Update tail and ring doorbell
    iosq->tail = (iosq->tail + 1) % iosq->entries;
    *iosq->db = iosq->tail;
    __threadfence_system();

    // Poll for completion
    NvmeCqe* cq_entry = reinterpret_cast<NvmeCqe*>(
        static_cast<char*>(iocq->vaddr) +
        (iocq->head * iocq->entry_size)
    );

    uint8_t expected_phase = iocq->phase;
    while (true) {
        uint8_t phase = cqe_phase(*cq_entry);
        if (phase == expected_phase && cq_entry->cid == cmd.cid) {
            break;
        }
        __threadfence_system();
    }

    // Update CQ head
    iocq->head = (iocq->head + 1) % iocq->entries;
    if (iocq->head == 0) {
        iocq->phase ^= 1;
    }
    *iocq->db = iocq->head;

    // Sum the data
    const uint32_t* data = reinterpret_cast<const uint32_t*>(gpu_buffer);
    uint32_t sum = 0;
    for (int i = 0; i < 1024; ++i) {  // 4KB / sizeof(uint32_t)
        sum += data[i];
    }
    *result = sum;

    // End timing
    clock_t end = clock64();
    *timing_ns = end - start;
}

/**
 * Parallel reduction sum after read
 */
__global__ void parallel_sum_kernel(const uint32_t* data, uint32_t* result) {
    __shared__ uint32_t sdata[256];

    unsigned int tid = threadIdx.x;
    unsigned int i = blockIdx.x * blockDim.x + threadIdx.x;

    // Load data
    sdata[tid] = (i < 1024) ? data[i] : 0;
    __syncthreads();

    // Reduce
    for (unsigned int s = blockDim.x / 2; s > 0; s >>= 1) {
        if (tid < s) {
            sdata[tid] += sdata[tid + s];
        }
        __syncthreads();
    }

    if (tid == 0) {
        atomicAdd(result, sdata[0]);
    }
}

/**
 * GPU Direct submission result
 */
struct GPUDirectResult {
    uint64_t total_ns;
    uint32_t sum;
    bool success;
};

/**
 * Launch GPU Direct read and sum
 */
extern "C" GPUDirectResult launch_gpu_direct_read_and_sum(
    Queue* iosq,
    Queue* iocq,
    uint64_t lba,
    void* gpu_buffer,
    uint64_t buffer_iova,
    cudaStream_t stream
) {
    GPUDirectResult result{};

    uint32_t* d_result;
    uint64_t* d_timing;
    cudaMalloc(&d_result, sizeof(uint32_t));
    cudaMalloc(&d_timing, sizeof(uint64_t));
    cudaMemset(d_result, 0, sizeof(uint32_t));

    // Launch kernel
    gpu_submit_read_and_sum_kernel<<<1, 1, 0, stream>>>(
        iosq, iocq, lba, gpu_buffer, buffer_iova,
        d_result, d_timing
    );

    cudaStreamSynchronize(stream);

    // Get results
    cudaMemcpy(&result.sum, d_result, sizeof(uint32_t), cudaMemcpyDeviceToHost);
    cudaMemcpy(&result.total_ns, d_timing, sizeof(uint64_t), cudaMemcpyDeviceToHost);

    cudaFree(d_result);
    cudaFree(d_timing);

    result.success = true;
    return result;
}
