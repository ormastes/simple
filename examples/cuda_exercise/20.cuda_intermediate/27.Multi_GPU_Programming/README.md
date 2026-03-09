# 🔗 Part 27: Multi-GPU Programming

**Goal**: Master multi-GPU programming by extending Module 26's cooperative groups patterns to distributed execution across multiple GPUs with efficient data distribution, peer-to-peer communication, and load balancing.

## Project Structure
```
27.Multi_GPU_Programming/
├── README.md                          - This documentation
├── CMakeLists.txt                     - Build configuration
├── src/
│   ├── CMakeLists.txt                 - Source build configuration
│   ├── host/                          - CPU-side multi-GPU management
│   │   ├── multi_gpu_manager.h        - MultiGPUManager class header
│   │   └── multi_gpu_manager.cpp      - MultiGPUManager implementation
│   └── kernels/                       - Multi-GPU CUDA kernels
│       ├── matrix_multiply_multi_gpu.cu - Multi-GPU matrix multiplication
│       └── vector_ops_multi_gpu.cu      - Multi-GPU vector operations
└── test/
    ├── CMakeLists.txt                 - Test build configuration
    └── unit/
        ├── host/
        │   └── test_multi_gpu_manager.cpp - Tests for MultiGPUManager
        └── kernels/
            ├── test_multi_gpu_matmul.cu   - Matrix multiplication tests
            └── test_multi_gpu_reduction.cu - Reduction and vector tests
```

## Quick Navigation
- [27.1 Introduction](#271-introduction-to-multi-gpu-programming)
- [27.2 Learning Objectives](#272-learning-objectives)
- [27.3 Multi-GPU System Architecture](#273-multi-gpu-system-architecture)
- [27.4 Multi-GPU Memory Management](#274-multi-gpu-memory-management)
- [27.5 Multi-GPU Kernel Execution](#275-multi-gpu-kernel-execution)
- [27.6 Advanced Multi-GPU Patterns](#276-advanced-multi-gpu-patterns)
- [27.7 Performance Optimization](#277-performance-optimization)
- [27.8 Practical Examples](#278-practical-examples)
- [27.9 Exercises](#279-exercises)
- [27.10 Building and Running](#2710-building-and-running)
- [27.11 Key Takeaways](#2711-key-takeaways)
- [Summary](#summary)

---

## **27.1 Introduction to Multi-GPU Programming**

Multi-GPU programming enables scaling computations across multiple graphics cards for maximum performance and parallel processing power. This module extends the cooperative groups patterns from Module 26 to distributed multi-GPU execution.

## 27.2 Learning Objectives

- Master multi-GPU system architecture and topology
- Implement efficient data distribution and load balancing
- Use peer-to-peer memory access and communication
- Design scalable multi-GPU algorithms
- Optimize memory transfers and synchronization

## 27.3 Multi-GPU System Architecture

### 27.3.1 GPU Topology Discovery

```cpp
#include <cuda_runtime.h>
#include <vector>

struct GPUInfo {
    int deviceId;
    cudaDeviceProp properties;
    std::vector<bool> canAccessPeer;
    std::vector<int> linkType;
    size_t totalMemory;
    size_t freeMemory;
};

class MultiGPUTopology {
private:
    std::vector<GPUInfo> gpus;
    int deviceCount;

public:
    void discoverTopology() {
        cudaGetDeviceCount(&deviceCount);
        gpus.resize(deviceCount);

        for (int i = 0; i < deviceCount; i++) {
            gpus[i].deviceId = i;
            cudaGetDeviceProperties(&gpus[i].properties, i);

            // Get memory information
            cudaSetDevice(i);
            cudaMemGetInfo(&gpus[i].freeMemory, &gpus[i].totalMemory);

            // Check peer access capabilities
            gpus[i].canAccessPeer.resize(deviceCount);
            gpus[i].linkType.resize(deviceCount);

            for (int j = 0; j < deviceCount; j++) {
                if (i != j) {
                    int canAccess;
                    cudaDeviceCanAccessPeer(&canAccess, i, j);
                    gpus[i].canAccessPeer[j] = (canAccess == 1);

                    // Determine link type (simplified)
                    if (canAccess) {
                        // In a real implementation, query actual link type
                        gpus[i].linkType[j] = 1; // 1=NVLink, 0=PCIe
                    }
                }
            }
        }

        printTopology();
    }

    void printTopology() {
        printf("Multi-GPU Topology:\n");
        printf("===================\n");

        for (int i = 0; i < deviceCount; i++) {
            printf("GPU %d: %s\n", i, gpus[i].properties.name);
            printf("  Memory: %.1f GB (%.1f GB free)\n",
                   gpus[i].totalMemory / 1e9,
                   gpus[i].freeMemory / 1e9);
            printf("  Compute Capability: %d.%d\n",
                   gpus[i].properties.major,
                   gpus[i].properties.minor);

            printf("  Peer Access: ");
            for (int j = 0; j < deviceCount; j++) {
                if (i != j) {
                    printf("GPU%d:%s ", j,
                           gpus[i].canAccessPeer[j] ? "YES" : "NO");
                }
            }
            printf("\n\n");
        }
    }

    int getDeviceCount() const { return deviceCount; }
    const GPUInfo& getGPU(int id) const { return gpus[id]; }
};
```

### 27.3.2 Peer Access Setup

```cpp
class PeerAccessManager {
private:
    int deviceCount;
    std::vector<std::vector<bool>> peerMatrix;

public:
    void setupPeerAccess() {
        cudaGetDeviceCount(&deviceCount);
        peerMatrix.resize(deviceCount, std::vector<bool>(deviceCount, false));

        // Enable peer access for all possible pairs
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);

            for (int j = 0; j < deviceCount; j++) {
                if (i != j) {
                    int canAccess;
                    cudaDeviceCanAccessPeer(&canAccess, i, j);

                    if (canAccess) {
                        cudaError_t err = cudaDeviceEnablePeerAccess(j, 0);
                        if (err == cudaSuccess) {
                            peerMatrix[i][j] = true;
                            printf("Enabled peer access: GPU %d -> GPU %d\n", i, j);
                        } else if (err != cudaErrorPeerAccessAlreadyEnabled) {
                            printf("Failed to enable peer access: GPU %d -> GPU %d\n", i, j);
                        }
                    }
                }
            }
        }
    }

    bool canAccessPeer(int src, int dst) const {
        return peerMatrix[src][dst];
    }

    void cleanup() {
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            for (int j = 0; j < deviceCount; j++) {
                if (peerMatrix[i][j]) {
                    cudaDeviceDisablePeerAccess(j);
                }
            }
        }
    }
};
```

## 27.4 Multi-GPU Memory Management

### 27.4.1 Distributed Memory Allocation

```cpp
template<typename T>
class MultiGPUBuffer {
private:
    struct DeviceBuffer {
        T* ptr;
        size_t size;
        int deviceId;
        cudaStream_t stream;
    };

    std::vector<DeviceBuffer> buffers;
    size_t totalElements;
    int deviceCount;

public:
    MultiGPUBuffer(size_t elements, int numDevices = -1) {
        if (numDevices == -1) {
            cudaGetDeviceCount(&numDevices);
        }

        deviceCount = numDevices;
        totalElements = elements;
        buffers.resize(deviceCount);

        // Distribute elements across devices
        size_t elementsPerDevice = (elements + deviceCount - 1) / deviceCount;

        for (int i = 0; i < deviceCount; i++) {
            buffers[i].deviceId = i;
            buffers[i].size = std::min(elementsPerDevice,
                                     elements - i * elementsPerDevice);

            cudaSetDevice(i);
            cudaMalloc(&buffers[i].ptr, buffers[i].size * sizeof(T));
            cudaStreamCreate(&buffers[i].stream);

            printf("GPU %d: allocated %zu elements\n", i, buffers[i].size);
        }
    }

    ~MultiGPUBuffer() {
        for (auto& buffer : buffers) {
            cudaSetDevice(buffer.deviceId);
            cudaFree(buffer.ptr);
            cudaStreamDestroy(buffer.stream);
        }
    }

    T* getDevicePtr(int deviceId) { return buffers[deviceId].ptr; }
    size_t getDeviceSize(int deviceId) { return buffers[deviceId].size; }
    cudaStream_t getStream(int deviceId) { return buffers[deviceId].stream; }

    void copyFromHost(const T* hostData) {
        size_t offset = 0;
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaMemcpyAsync(buffers[i].ptr,
                           hostData + offset,
                           buffers[i].size * sizeof(T),
                           cudaMemcpyHostToDevice,
                           buffers[i].stream);
            offset += buffers[i].size;
        }

        // Synchronize all streams
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaStreamSynchronize(buffers[i].stream);
        }
    }

    void copyToHost(T* hostData) {
        size_t offset = 0;
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaMemcpyAsync(hostData + offset,
                           buffers[i].ptr,
                           buffers[i].size * sizeof(T),
                           cudaMemcpyDeviceToHost,
                           buffers[i].stream);
            offset += buffers[i].size;
        }

        // Synchronize all streams
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaStreamSynchronize(buffers[i].stream);
        }
    }
};
```

### 27.4.2 Peer-to-Peer Memory Transfer

```cpp
class P2PTransferManager {
private:
    int deviceCount;
    PeerAccessManager* peerManager;

public:
    P2PTransferManager(PeerAccessManager* pm) : peerManager(pm) {
        cudaGetDeviceCount(&deviceCount);
    }

    void directP2PTransfer(void* dst, int dstDevice,
                          const void* src, int srcDevice,
                          size_t size, cudaStream_t stream = 0) {
        if (peerManager->canAccessPeer(dstDevice, srcDevice)) {
            // Direct peer-to-peer copy
            cudaSetDevice(dstDevice);
            cudaMemcpyPeerAsync(dst, dstDevice,
                               src, srcDevice,
                               size, stream);
        } else {
            // Fallback through host memory
            transferThroughHost(dst, dstDevice, src, srcDevice, size, stream);
        }
    }

    void transferThroughHost(void* dst, int dstDevice,
                           const void* src, int srcDevice,
                           size_t size, cudaStream_t stream) {
        // Allocate pinned host memory for staging
        void* hostBuffer;
        cudaMallocHost(&hostBuffer, size);

        // Device -> Host
        cudaSetDevice(srcDevice);
        cudaMemcpyAsync(hostBuffer, src, size,
                       cudaMemcpyDeviceToHost, stream);
        cudaStreamSynchronize(stream);

        // Host -> Device
        cudaSetDevice(dstDevice);
        cudaMemcpyAsync(dst, hostBuffer, size,
                       cudaMemcpyHostToDevice, stream);
        cudaStreamSynchronize(stream);

        cudaFreeHost(hostBuffer);
    }

    void broadcastData(void** dstPtrs, int* dstDevices, int numDst,
                      const void* src, int srcDevice, size_t size) {
        std::vector<cudaStream_t> streams(numDst);

        for (int i = 0; i < numDst; i++) {
            cudaSetDevice(dstDevices[i]);
            cudaStreamCreate(&streams[i]);
        }

        // Broadcast to all devices
        for (int i = 0; i < numDst; i++) {
            directP2PTransfer(dstPtrs[i], dstDevices[i],
                             src, srcDevice, size, streams[i]);
        }

        // Synchronize all transfers
        for (int i = 0; i < numDst; i++) {
            cudaSetDevice(dstDevices[i]);
            cudaStreamSynchronize(streams[i]);
            cudaStreamDestroy(streams[i]);
        }
    }

    void allGather(void** buffers, int* devices, int numDevices,
                   size_t elementSize, size_t elementsPerDevice) {
        // Each device gathers data from all other devices
        for (int dst = 0; dst < numDevices; dst++) {
            for (int src = 0; src < numDevices; src++) {
                if (dst != src) {
                    void* dstPtr = (char*)buffers[dst] + src * elementsPerDevice * elementSize;
                    void* srcPtr = buffers[src];

                    directP2PTransfer(dstPtr, devices[dst],
                                     srcPtr, devices[src],
                                     elementsPerDevice * elementSize);
                }
            }
        }
    }
};
```

## 27.5 Multi-GPU Kernel Execution

### 27.5.1 Distributed Kernel Launch

```cpp
template<typename KernelFunc, typename... Args>
class MultiGPUKernelLauncher {
private:
    int deviceCount;
    std::vector<cudaStream_t> streams;

public:
    MultiGPUKernelLauncher() {
        cudaGetDeviceCount(&deviceCount);
        streams.resize(deviceCount);

        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaStreamCreate(&streams[i]);
        }
    }

    ~MultiGPUKernelLauncher() {
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaStreamDestroy(streams[i]);
        }
    }

    void launchDistributed(KernelFunc kernel,
                          dim3 totalGrid, dim3 block,
                          Args... args) {
        // Distribute grid across devices
        int gridsPerDevice = (totalGrid.x + deviceCount - 1) / deviceCount;

        for (int dev = 0; dev < deviceCount; dev++) {
            cudaSetDevice(dev);

            int startGrid = dev * gridsPerDevice;
            int endGrid = std::min((dev + 1) * gridsPerDevice, (int)totalGrid.x);
            int actualGrids = endGrid - startGrid;

            if (actualGrids > 0) {
                dim3 deviceGrid(actualGrids, totalGrid.y, totalGrid.z);

                // Launch kernel with offset parameters
                kernel<<<deviceGrid, block, 0, streams[dev]>>>(
                    startGrid, args...);
            }
        }
    }

    void synchronizeAll() {
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaStreamSynchronize(streams[i]);
        }
    }
};

// Example kernel that handles multi-GPU indexing
__global__ void multiGPUVectorAdd(int gridOffset, float* a, float* b, float* c, int n) {
    int globalIdx = (blockIdx.x + gridOffset) * blockDim.x + threadIdx.x;

    if (globalIdx < n) {
        c[globalIdx] = a[globalIdx] + b[globalIdx];
    }
}
```

### 27.5.2 Load Balancing Strategies

```cpp
class LoadBalancer {
private:
    struct DeviceMetrics {
        float computeCapabilityScore;
        float memoryBandwidth;
        int coreCount;
        float performanceWeight;
    };

    std::vector<DeviceMetrics> deviceMetrics;
    int deviceCount;

public:
    void initializeMetrics() {
        cudaGetDeviceCount(&deviceCount);
        deviceMetrics.resize(deviceCount);

        for (int i = 0; i < deviceCount; i++) {
            cudaDeviceProp prop;
            cudaGetDeviceProperties(&prop, i);

            deviceMetrics[i].computeCapabilityScore =
                prop.major * 10 + prop.minor;
            deviceMetrics[i].memoryBandwidth = prop.memoryClockRate * prop.memoryBusWidth / 8.0f;
            deviceMetrics[i].coreCount = prop.multiProcessorCount;

            // Compute relative performance weight
            deviceMetrics[i].performanceWeight =
                deviceMetrics[i].computeCapabilityScore *
                deviceMetrics[i].memoryBandwidth *
                deviceMetrics[i].coreCount;
        }

        // Normalize weights
        float totalWeight = 0.0f;
        for (auto& metric : deviceMetrics) {
            totalWeight += metric.performanceWeight;
        }

        for (auto& metric : deviceMetrics) {
            metric.performanceWeight /= totalWeight;
        }
    }

    std::vector<int> distributeWork(int totalWork) {
        std::vector<int> workDistribution(deviceCount);

        for (int i = 0; i < deviceCount; i++) {
            workDistribution[i] = (int)(totalWork * deviceMetrics[i].performanceWeight);
        }

        // Adjust for rounding errors
        int assignedWork = 0;
        for (int work : workDistribution) {
            assignedWork += work;
        }

        // Assign remaining work to the most capable device
        int remaining = totalWork - assignedWork;
        if (remaining > 0) {
            int bestDevice = 0;
            float bestScore = deviceMetrics[0].performanceWeight;
            for (int i = 1; i < deviceCount; i++) {
                if (deviceMetrics[i].performanceWeight > bestScore) {
                    bestScore = deviceMetrics[i].performanceWeight;
                    bestDevice = i;
                }
            }
            workDistribution[bestDevice] += remaining;
        }

        return workDistribution;
    }

    void printDistribution(const std::vector<int>& distribution) {
        printf("Work Distribution:\n");
        for (int i = 0; i < deviceCount; i++) {
            printf("GPU %d: %d units (%.1f%%, weight: %.3f)\n",
                   i, distribution[i],
                   100.0f * distribution[i] /
                   std::accumulate(distribution.begin(), distribution.end(), 0),
                   deviceMetrics[i].performanceWeight);
        }
    }
};
```

## 27.6 Advanced Multi-GPU Patterns

### 27.6.1 Pipelined Processing

```cpp
template<int STAGES>
class MultiGPUPipeline {
private:
    struct PipelineStage {
        int deviceId;
        cudaStream_t stream;
        void* inputBuffer;
        void* outputBuffer;
        size_t bufferSize;
    };

    std::vector<PipelineStage> stages;
    P2PTransferManager* transferManager;

public:
    MultiGPUPipeline(size_t bufferSize, P2PTransferManager* tm)
        : transferManager(tm) {
        stages.resize(STAGES);

        for (int i = 0; i < STAGES; i++) {
            stages[i].deviceId = i % deviceCount;
            stages[i].bufferSize = bufferSize;

            cudaSetDevice(stages[i].deviceId);
            cudaStreamCreate(&stages[i].stream);
            cudaMalloc(&stages[i].inputBuffer, bufferSize);
            cudaMalloc(&stages[i].outputBuffer, bufferSize);
        }
    }

    void processBatch(void* inputData, void* outputData, size_t dataSize) {
        // Stage 0: Initial data load
        cudaSetDevice(stages[0].deviceId);
        cudaMemcpyAsync(stages[0].inputBuffer, inputData, dataSize,
                       cudaMemcpyHostToDevice, stages[0].stream);

        // Pipeline execution
        for (int stage = 0; stage < STAGES; stage++) {
            cudaSetDevice(stages[stage].deviceId);

            // Execute stage-specific kernel
            executeStageKernel(stage, stages[stage].inputBuffer,
                             stages[stage].outputBuffer,
                             stages[stage].stream);

            // Transfer to next stage (if not last)
            if (stage < STAGES - 1) {
                int nextDevice = stages[stage + 1].deviceId;
                transferManager->directP2PTransfer(
                    stages[stage + 1].inputBuffer, nextDevice,
                    stages[stage].outputBuffer, stages[stage].deviceId,
                    dataSize, stages[stage].stream);
            }
        }

        // Final data retrieval
        int lastStage = STAGES - 1;
        cudaSetDevice(stages[lastStage].deviceId);
        cudaMemcpyAsync(outputData, stages[lastStage].outputBuffer, dataSize,
                       cudaMemcpyDeviceToHost, stages[lastStage].stream);

        // Synchronize final stage
        cudaStreamSynchronize(stages[lastStage].stream);
    }

private:
    void executeStageKernel(int stage, void* input, void* output, cudaStream_t stream) {
        // Launch stage-specific kernel
        dim3 grid(256), block(256);

        switch (stage) {
            case 0:
                stage0Kernel<<<grid, block, 0, stream>>>(
                    (float*)input, (float*)output);
                break;
            case 1:
                stage1Kernel<<<grid, block, 0, stream>>>(
                    (float*)input, (float*)output);
                break;
            // ... more stages
        }
    }
};
```

### 27.6.2 Reduction Across Multiple GPUs

```cpp
template<typename T>
class MultiGPUReduction {
private:
    struct ReduceBuffer {
        T* data;
        T* partialResults;
        size_t size;
        int deviceId;
        cudaStream_t stream;
    };

    std::vector<ReduceBuffer> buffers;
    P2PTransferManager* transferManager;
    int deviceCount;

public:
    MultiGPUReduction(P2PTransferManager* tm) : transferManager(tm) {
        cudaGetDeviceCount(&deviceCount);
        buffers.resize(deviceCount);
    }

    void setupBuffers(size_t elementsPerDevice) {
        for (int i = 0; i < deviceCount; i++) {
            buffers[i].deviceId = i;
            buffers[i].size = elementsPerDevice;

            cudaSetDevice(i);
            cudaMalloc(&buffers[i].data, elementsPerDevice * sizeof(T));
            cudaMalloc(&buffers[i].partialResults, sizeof(T));
            cudaStreamCreate(&buffers[i].stream);
        }
    }

    T reduce(const std::vector<T*>& deviceData) {
        // Phase 1: Local reduction on each device
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);

            // Launch local reduction kernel
            localReduceKernel<<<256, 256, 0, buffers[i].stream>>>(
                deviceData[i], buffers[i].partialResults, buffers[i].size);
        }

        // Synchronize local reductions
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaStreamSynchronize(buffers[i].stream);
        }

        // Phase 2: Tree reduction across devices
        return treeReduction();
    }

private:
    T treeReduction() {
        int activeDevices = deviceCount;
        std::vector<int> activeList(deviceCount);
        std::iota(activeList.begin(), activeList.end(), 0);

        while (activeDevices > 1) {
            int pairs = activeDevices / 2;

            for (int p = 0; p < pairs; p++) {
                int srcDevice = activeList[p * 2 + 1];
                int dstDevice = activeList[p * 2];

                // Transfer partial result from src to dst
                transferManager->directP2PTransfer(
                    (char*)buffers[dstDevice].partialResults + sizeof(T),
                    dstDevice,
                    buffers[srcDevice].partialResults,
                    srcDevice,
                    sizeof(T));

                // Combine results on destination device
                cudaSetDevice(dstDevice);
                combineResultsKernel<<<1, 1, 0, buffers[dstDevice].stream>>>(
                    buffers[dstDevice].partialResults,
                    (T*)((char*)buffers[dstDevice].partialResults + sizeof(T)));

                cudaStreamSynchronize(buffers[dstDevice].stream);
            }

            // Handle odd device
            if (activeDevices % 2 == 1) {
                activeList[pairs] = activeList[activeDevices - 1];
                activeDevices = pairs + 1;
            } else {
                activeDevices = pairs;
            }
        }

        // Get final result from device 0
        T result;
        cudaSetDevice(0);
        cudaMemcpy(&result, buffers[0].partialResults, sizeof(T),
                  cudaMemcpyDeviceToHost);

        return result;
    }
};

// Example kernels for reduction
__global__ void localReduceKernel(float* input, float* output, int n) {
    __shared__ float shared[256];

    int tid = threadIdx.x;
    int idx = blockIdx.x * blockDim.x + threadIdx.x;

    // Load data
    shared[tid] = (idx < n) ? input[idx] : 0.0f;
    __syncthreads();

    // Reduce within block
    for (int stride = blockDim.x / 2; stride > 0; stride >>= 1) {
        if (tid < stride) {
            shared[tid] += shared[tid + stride];
        }
        __syncthreads();
    }

    // Write block result
    if (tid == 0) {
        atomicAdd(output, shared[0]);
    }
}

__global__ void combineResultsKernel(float* result1, float* result2) {
    *result1 += *result2;
}
```

## 27.7 Performance Optimization

### 27.7.1 Memory Transfer Optimization

```cpp
class MultiGPUTransferOptimizer {
private:
    struct TransferMetrics {
        float bandwidthGBps;
        float latencyMs;
        int linkType; // 0=PCIe, 1=NVLink
    };

    std::vector<std::vector<TransferMetrics>> transferMatrix;
    int deviceCount;

public:
    void benchmarkTransfers() {
        cudaGetDeviceCount(&deviceCount);
        transferMatrix.resize(deviceCount,
                            std::vector<TransferMetrics>(deviceCount));

        const size_t benchmarkSize = 1024 * 1024 * 1024; // 1GB
        const int iterations = 10;

        for (int src = 0; src < deviceCount; src++) {
            for (int dst = 0; dst < deviceCount; dst++) {
                if (src != dst) {
                    transferMatrix[src][dst] =
                        benchmarkP2PTransfer(src, dst, benchmarkSize, iterations);
                }
            }
        }

        printTransferMatrix();
    }

private:
    TransferMetrics benchmarkP2PTransfer(int src, int dst,
                                       size_t size, int iterations) {
        void *srcPtr, *dstPtr;
        cudaSetDevice(src);
        cudaMalloc(&srcPtr, size);

        cudaSetDevice(dst);
        cudaMalloc(&dstPtr, size);

        cudaEvent_t start, stop;
        cudaEventCreate(&start);
        cudaEventCreate(&stop);

        // Warm up
        for (int i = 0; i < 3; i++) {
            cudaMemcpyPeer(dstPtr, dst, srcPtr, src, size);
        }

        cudaDeviceSynchronize();

        // Benchmark
        cudaEventRecord(start);
        for (int i = 0; i < iterations; i++) {
            cudaMemcpyPeer(dstPtr, dst, srcPtr, src, size);
        }
        cudaEventRecord(stop);
        cudaEventSynchronize(stop);

        float totalTimeMs;
        cudaEventElapsedTime(&totalTimeMs, start, stop);

        TransferMetrics metrics;
        metrics.latencyMs = totalTimeMs / iterations;
        metrics.bandwidthGBps = (size * iterations / 1e9) / (totalTimeMs / 1000.0f);

        // Determine link type based on bandwidth
        metrics.linkType = (metrics.bandwidthGBps > 20.0f) ? 1 : 0;

        // Cleanup
        cudaSetDevice(src);
        cudaFree(srcPtr);
        cudaSetDevice(dst);
        cudaFree(dstPtr);
        cudaEventDestroy(start);
        cudaEventDestroy(stop);

        return metrics;
    }

    void printTransferMatrix() {
        printf("\nP2P Transfer Performance Matrix:\n");
        printf("Source -> Destination: Bandwidth (GB/s) [Link Type]\n");
        printf("========================================================\n");

        for (int src = 0; src < deviceCount; src++) {
            for (int dst = 0; dst < deviceCount; dst++) {
                if (src != dst) {
                    printf("GPU%d -> GPU%d: %.1f GB/s [%s]\n",
                           src, dst,
                           transferMatrix[src][dst].bandwidthGBps,
                           transferMatrix[src][dst].linkType ? "NVLink" : "PCIe");
                }
            }
        }
    }
};
```

### 27.7.2 Synchronization Optimization

```cpp
class MultiGPUSynchronizer {
private:
    std::vector<cudaEvent_t> events;
    std::vector<cudaStream_t> streams;
    int deviceCount;

public:
    MultiGPUSynchronizer() {
        cudaGetDeviceCount(&deviceCount);
        events.resize(deviceCount);
        streams.resize(deviceCount);

        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaEventCreate(&events[i]);
            cudaStreamCreate(&streams[i]);
        }
    }

    ~MultiGPUSynchronizer() {
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaEventDestroy(events[i]);
            cudaStreamDestroy(streams[i]);
        }
    }

    void recordEvents() {
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaEventRecord(events[i], streams[i]);
        }
    }

    void waitForAll() {
        for (int i = 0; i < deviceCount; i++) {
            cudaSetDevice(i);
            cudaEventSynchronize(events[i]);
        }
    }

    void crossDeviceSync() {
        // Each device waits for all other devices
        for (int dst = 0; dst < deviceCount; dst++) {
            cudaSetDevice(dst);
            for (int src = 0; src < deviceCount; src++) {
                if (src != dst) {
                    cudaStreamWaitEvent(streams[dst], events[src], 0);
                }
            }
        }
    }

    void barrierSync() {
        // Record events on all devices
        recordEvents();

        // Wait for all events to complete
        waitForAll();
    }
};
```

## 27.8 Practical Examples

### 27.8.1 Multi-GPU Matrix Multiplication

```cpp
template<typename T>
class MultiGPUMatMul {
private:
    MultiGPUBuffer<T>* matrixA;
    MultiGPUBuffer<T>* matrixB;
    MultiGPUBuffer<T>* matrixC;
    P2PTransferManager* transferManager;
    int deviceCount;

public:
    MultiGPUMatMul(int M, int N, int K, P2PTransferManager* tm)
        : transferManager(tm) {
        cudaGetDeviceCount(&deviceCount);

        // Distribute matrices across devices
        matrixA = new MultiGPUBuffer<T>(M * K, deviceCount);
        matrixB = new MultiGPUBuffer<T>(K * N, deviceCount);
        matrixC = new MultiGPUBuffer<T>(M * N, deviceCount);
    }

    void multiply(const T* hostA, const T* hostB, T* hostC,
                 int M, int N, int K) {
        // Load input matrices
        matrixA->copyFromHost(hostA);
        matrixB->copyFromHost(hostB);

        // Distribute computation across devices
        int rowsPerDevice = (M + deviceCount - 1) / deviceCount;

        for (int dev = 0; dev < deviceCount; dev++) {
            cudaSetDevice(dev);

            int startRow = dev * rowsPerDevice;
            int endRow = std::min((dev + 1) * rowsPerDevice, M);
            int actualRows = endRow - startRow;

            if (actualRows > 0) {
                // Launch matrix multiplication kernel
                dim3 block(16, 16);
                dim3 grid((N + block.x - 1) / block.x,
                         (actualRows + block.y - 1) / block.y);

                matmulKernel<<<grid, block, 0, matrixC->getStream(dev)>>>(
                    matrixA->getDevicePtr(dev),
                    matrixB->getDevicePtr(dev),
                    matrixC->getDevicePtr(dev),
                    M, N, K, startRow, actualRows);
            }
        }

        // Synchronize all devices
        for (int dev = 0; dev < deviceCount; dev++) {
            cudaSetDevice(dev);
            cudaStreamSynchronize(matrixC->getStream(dev));
        }

        // Gather results
        matrixC->copyToHost(hostC);
    }
};

__global__ void matmulKernel(float* A, float* B, float* C,
                           int M, int N, int K,
                           int rowOffset, int numRows) {
    int col = blockIdx.x * blockDim.x + threadIdx.x;
    int row = blockIdx.y * blockDim.y + threadIdx.y;

    if (row < numRows && col < N) {
        float sum = 0.0f;
        int globalRow = rowOffset + row;

        for (int k = 0; k < K; k++) {
            sum += A[globalRow * K + k] * B[k * N + col];
        }

        C[globalRow * N + col] = sum;
    }
}
```

## 27.9 Exercises

1. **Topology Analysis**: Implement a tool to analyze multi-GPU system topology
2. **Load Balancing**: Design dynamic load balancing for heterogeneous GPU systems
3. **Communication Patterns**: Implement all-reduce and broadcast operations
4. **Pipelined Algorithm**: Create a multi-stage pipeline across GPUs
5. **Performance Study**: Compare single-GPU vs multi-GPU performance

## 27.10 Building and Running

```bash
# Build with multi-GPU examples
cd build/30.cuda_advanced/27.Multi_GPU_Programming
ninja

# Run examples
./39_MultiGPU_topology
./39_MultiGPU_reduction
./39_MultiGPU_matmul

# Profile multi-GPU operations
ncu --target-processes all --replay-mode kernel \
    ./39_MultiGPU_matmul

# Analyze P2P transfers
nsys profile --stats=true -t cuda,nvtx \
    ./39_MultiGPU_reduction
```

## 27.11 Key Takeaways

- Multi-GPU programming requires careful topology analysis and peer access setup
- Effective load balancing is crucial for heterogeneous GPU systems
- P2P transfers can significantly improve performance over host-based transfers
- Pipelined processing patterns enable efficient multi-GPU algorithms
- Synchronization overhead must be minimized for scalable performance
- Understanding memory hierarchy is essential for optimal data placement

---

## ✅ **Summary**

### **Key Takeaways**

1. **Multi-GPU Architecture and Topology:**
   - Discovered GPU topology with peer access capabilities (NVLink vs PCIe)
   - Enabled peer-to-peer memory access for direct GPU-to-GPU transfers
   - Implemented `MultiGPUManager` for centralized multi-GPU resource management
   - Measured P2P transfer bandwidth to guide algorithmic choices

2. **Data Distribution Strategies:**
   - Row-wise distribution for matrix operations (minimal communication)
   - Element-wise distribution for vector operations (perfect load balance)
   - Replicated data (matrix B) vs P2P access trade-offs
   - Load balancing based on GPU compute capabilities and SM counts

3. **Multi-GPU Kernel Patterns:**
   - **Matrix Multiplication:** Distribute rows of A, replicate B, compute C in parallel
   - **Reduction:** Local reduction on each GPU → tree-based combining → single result
   - **Vector Operations:** Independent processing on local data with minimal sync
   - **Histogram:** Local histograms with final merge step

4. **Communication and Synchronization:**
   - Peer-to-peer transfers for low-latency GPU-to-GPU communication
   - Asynchronous streams for overlapping computation and transfer
   - Event-based synchronization for cross-device coordination
   - Host-based fallback for non-P2P capable systems

5. **Performance Comparison:**
   - **Single GPU:** Full dataset on one device, all memory local
   - **Multi-GPU (Replicated B):** 2-4x speedup for large matrices (near-linear scaling)
   - **Multi-GPU (P2P B):** Depends on interconnect bandwidth (NVLink: good, PCIe: poor)
   - **Bottlenecks:** Data transfer overhead, load imbalance, synchronization cost

### **Module 26 vs Module 27**

| Aspect | Module 26 (Single GPU) | Module 27 (Multi-GPU) | Enhancement |
|--------|----------------------|---------------------|-------------|
| **Execution** | All threads on one GPU | Distributed across GPUs | N× parallel capacity |
| **Memory** | Single device memory | Distributed + P2P access | Larger datasets |
| **Kernels** | Cooperative groups | Multi-GPU aware kernels | Explicit data distribution |
| **Synchronization** | Block/grid sync | Cross-device events | Hierarchical sync |
| **Scalability** | Limited by single GPU | Near-linear scaling | 2-4× speedup (2-4 GPUs) |

### **Implementation Highlights**

**Source Code References:**
- `src/kernels/matrix_multiply_multi_gpu.cu:36-87` - Multi-GPU tiled matmul
- `src/kernels/vector_ops_multi_gpu.cu:31-84` - Multi-GPU reduction local phase
- `src/host/multi_gpu_manager.cpp:14-69` - Peer access setup and topology discovery

**Test Coverage:**
- ✅ Multi-GPU matrix multiplication with data distribution
- ✅ Multi-GPU reduction with tree-based combining
- ✅ Load balancing and work distribution
- ✅ Peer access setup and topology queries
- ✅ Vector addition across distributed data

### **Performance Metrics**

**2-GPU System (Example Results):**
- Matrix Multiplication (2048×2048): 1.8× speedup vs single GPU
- Reduction (10M elements): 1.9× speedup vs single GPU
- Vector Add (10M elements): 1.95× speedup vs single GPU (near-perfect)
- P2P Bandwidth: 40 GB/s (NVLink) vs 12 GB/s (PCIe)

**Bottlenecks:**
- Data transfer overhead for small workloads
- Load imbalance for heterogeneous GPUs
- Synchronization cost for fine-grained operations
- P2P bandwidth limits for frequent communication

### **Best Practices**

1. **Choose the Right Strategy:**
   - Replicate small data (< 100 MB) for simplicity
   - Use P2P for large shared data (> 1 GB) with NVLink
   - Fall back to host staging for PCIe-only systems

2. **Optimize Data Distribution:**
   - Balance work based on GPU capabilities (SM count, memory bandwidth)
   - Minimize cross-GPU communication (partition for locality)
   - Use async transfers to overlap with computation

3. **Synchronization:**
   - Minimize global synchronization points
   - Use event-based sync for fine-grained coordination
   - Batch operations to amortize sync overhead

### **Common Errors & Solutions**

| Error | Cause | Solution |
|-------|-------|----------|
| `cudaErrorPeerAccessAlreadyEnabled` | Calling `cudaDeviceEnablePeerAccess` twice | Check if already enabled or clear error |
| `cudaErrorInvalidDevice` | Invalid device ID | Verify device count with `cudaGetDeviceCount` |
| Incorrect results | Data distribution mismatch | Verify offsets and sizes match distribution |
| Poor scaling | Excessive synchronization | Profile with `nsys` and reduce sync points |
| Low P2P bandwidth | Using PCIe instead of NVLink | Check topology, consider replicating data |

### **Next Steps**

- 📚 Return to [Part 26: Cooperative Groups](../26.Cooperative_Groups/README.md) for single-GPU patterns
- 🔧 Experiment with different data distribution strategies
- 📊 Profile multi-GPU applications with `nsys profile --target-processes all`
- 🎯 Apply multi-GPU patterns to your own large-scale problems
- 🔍 Explore NCCL library for advanced multi-GPU collectives

### **References**

- [CUDA Multi-GPU Programming Guide](https://docs.nvidia.com/cuda/cuda-c-programming-guide/#multi-device-programming)
- [Peer-to-Peer Memory Access](https://docs.nvidia.com/cuda/cuda-c-programming-guide/#peer-to-peer-memory-access)
- [CUDA Stream Semantics](https://docs.nvidia.com/cuda/cuda-c-programming-guide/#stream-semantics)
- Module 26: Cooperative Groups (single-GPU baseline)
- [NCCL: NVIDIA Collective Communications Library](https://developer.nvidia.com/nccl)

---

📄 **Previous**: [Part 26: Cooperative Groups](../26.Cooperative_Groups/README.md)
📄 **Next**: Part 28: Advanced Topics (TBD)
