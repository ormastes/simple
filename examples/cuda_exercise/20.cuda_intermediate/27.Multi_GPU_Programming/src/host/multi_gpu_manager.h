/**
 * Multi-GPU Manager Header (Module 27)
 *
 * Provides high-level abstractions for multi-GPU programming
 */

#pragma once

#include <cuda_runtime.h>
#include <vector>

/**
 * MultiGPUManager - Central manager for multi-GPU operations
 *
 * Handles:
 * - GPU topology discovery
 * - Peer access setup
 * - Stream management
 * - Work distribution
 * - Synchronization
 */
class MultiGPUManager {
public:
    MultiGPUManager();
    ~MultiGPUManager();

    // Initialization
    bool setupPeerAccess();
    void disablePeerAccess();

    // Query
    int getDeviceCount() const { return deviceCount; }
    bool isInitialized() const { return initialized; }
    bool canAccessPeer(int srcDevice, int dstDevice) const;
    const cudaDeviceProp& getDeviceProperties(int device) const;
    cudaStream_t getStream(int device) const;

    // Work distribution
    std::vector<int> distributeWork(int totalWork) const;

    // Synchronization
    void synchronizeAll() const;

    // Utilities
    void printTopology() const;

private:
    int deviceCount;
    bool initialized;
    std::vector<cudaDeviceProp> deviceProps;
    std::vector<cudaStream_t> streams;
    std::vector<std::vector<bool>> peerAccessMatrix;
};

/**
 * MultiGPUBuffer - Distributed buffer across multiple GPUs
 *
 * Automatically distributes data across GPUs and provides
 * unified interface for host-device transfers
 */
template<typename T>
class MultiGPUBuffer {
public:
    struct DeviceBuffer {
        T* ptr;
        size_t size;
        int deviceId;
    };

    MultiGPUBuffer(size_t totalElements, const MultiGPUManager& manager)
        : totalElements(totalElements), mgr(&manager) {

        int deviceCount = manager.getDeviceCount();
        buffers.resize(deviceCount);

        // Distribute elements across devices
        auto distribution = manager.distributeWork(totalElements);

        size_t offset = 0;
        for (int i = 0; i < deviceCount; i++) {
            buffers[i].deviceId = i;
            buffers[i].size = distribution[i];

            cudaSetDevice(i);
            cudaMalloc(&buffers[i].ptr, buffers[i].size * sizeof(T));

            printf("GPU %d: allocated %zu elements (offset: %zu)\n",
                   i, buffers[i].size, offset);

            offset += buffers[i].size;
        }
    }

    ~MultiGPUBuffer() {
        for (auto& buffer : buffers) {
            cudaSetDevice(buffer.deviceId);
            cudaFree(buffer.ptr);
        }
    }

    void copyFromHost(const T* hostData) {
        size_t offset = 0;
        for (int i = 0; i < static_cast<int>(buffers.size()); i++) {
            cudaSetDevice(i);
            cudaMemcpyAsync(buffers[i].ptr,
                           hostData + offset,
                           buffers[i].size * sizeof(T),
                           cudaMemcpyHostToDevice,
                           mgr->getStream(i));
            offset += buffers[i].size;
        }

        mgr->synchronizeAll();
    }

    void copyToHost(T* hostData) {
        size_t offset = 0;
        for (int i = 0; i < static_cast<int>(buffers.size()); i++) {
            cudaSetDevice(i);
            cudaMemcpyAsync(hostData + offset,
                           buffers[i].ptr,
                           buffers[i].size * sizeof(T),
                           cudaMemcpyDeviceToHost,
                           mgr->getStream(i));
            offset += buffers[i].size;
        }

        mgr->synchronizeAll();
    }

    T* getDevicePtr(int deviceId) const {
        return buffers[deviceId].ptr;
    }

    size_t getDeviceSize(int deviceId) const {
        return buffers[deviceId].size;
    }

    size_t getTotalSize() const {
        return totalElements;
    }

    const std::vector<DeviceBuffer>& getBuffers() const {
        return buffers;
    }

private:
    size_t totalElements;
    const MultiGPUManager* mgr;
    std::vector<DeviceBuffer> buffers;
};
