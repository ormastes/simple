/**
 * Multi-GPU Manager (Module 27)
 *
 * Provides high-level abstractions for multi-GPU programming:
 * - GPU topology discovery and peer access setup
 * - Memory allocation and distribution across GPUs
 * - Synchronization and data transfer utilities
 * - Load balancing and work distribution
 */

#include "multi_gpu_manager.h"
#include <algorithm>
#include <numeric>
#include <cstdio>

// ============================================================================
// MultiGPUManager Implementation
// ============================================================================

MultiGPUManager::MultiGPUManager() : initialized(false) {
    cudaGetDeviceCount(&deviceCount);

    if (deviceCount == 0) {
        fprintf(stderr, "No CUDA devices found!\n");
        return;
    }

    printf("Found %d CUDA device(s)\n", deviceCount);

    // Allocate per-device resources
    deviceProps.resize(deviceCount);
    streams.resize(deviceCount);
    peerAccessMatrix.resize(deviceCount, std::vector<bool>(deviceCount, false));

    // Get device properties
    for (int i = 0; i < deviceCount; i++) {
        cudaSetDevice(i);
        cudaGetDeviceProperties(&deviceProps[i], i);
        cudaStreamCreate(&streams[i]);

        printf("GPU %d: %s\n", i, deviceProps[i].name);
        printf("  Compute Capability: %d.%d\n",
               deviceProps[i].major, deviceProps[i].minor);
        printf("  Global Memory: %.1f GB\n",
               deviceProps[i].totalGlobalMem / 1e9);
        printf("  Multiprocessors: %d\n",
               deviceProps[i].multiProcessorCount);
    }

    initialized = true;
}

MultiGPUManager::~MultiGPUManager() {
    if (!initialized) return;

    // Destroy streams
    for (int i = 0; i < deviceCount; i++) {
        cudaSetDevice(i);
        cudaStreamDestroy(streams[i]);
    }

    // Disable peer access
    disablePeerAccess();
}

bool MultiGPUManager::setupPeerAccess() {
    if (!initialized) return false;

    printf("\nSetting up peer access...\n");

    for (int i = 0; i < deviceCount; i++) {
        cudaSetDevice(i);

        for (int j = 0; j < deviceCount; j++) {
            if (i != j) {
                int canAccess;
                cudaDeviceCanAccessPeer(&canAccess, i, j);

                if (canAccess) {
                    cudaError_t err = cudaDeviceEnablePeerAccess(j, 0);

                    if (err == cudaSuccess) {
                        peerAccessMatrix[i][j] = true;
                        printf("  GPU %d -> GPU %d: Enabled\n", i, j);
                    } else if (err == cudaErrorPeerAccessAlreadyEnabled) {
                        peerAccessMatrix[i][j] = true;
                        cudaGetLastError(); // Clear error
                    } else {
                        printf("  GPU %d -> GPU %d: Failed (%s)\n",
                               i, j, cudaGetErrorString(err));
                    }
                } else {
                    printf("  GPU %d -> GPU %d: Not supported\n", i, j);
                }
            }
        }
    }

    return true;
}

void MultiGPUManager::disablePeerAccess() {
    for (int i = 0; i < deviceCount; i++) {
        cudaSetDevice(i);

        for (int j = 0; j < deviceCount; j++) {
            if (peerAccessMatrix[i][j]) {
                cudaDeviceDisablePeerAccess(j);
                peerAccessMatrix[i][j] = false;
            }
        }
    }
}

bool MultiGPUManager::canAccessPeer(int srcDevice, int dstDevice) const {
    if (srcDevice < 0 || srcDevice >= deviceCount) return false;
    if (dstDevice < 0 || dstDevice >= deviceCount) return false;
    if (srcDevice == dstDevice) return false;

    return peerAccessMatrix[srcDevice][dstDevice];
}

std::vector<int> MultiGPUManager::distributeWork(int totalWork) const {
    std::vector<int> distribution(deviceCount);

    if (deviceCount == 1) {
        distribution[0] = totalWork;
        return distribution;
    }

    // Calculate performance weights based on SM count
    std::vector<float> weights(deviceCount);
    float totalWeight = 0.0f;

    for (int i = 0; i < deviceCount; i++) {
        weights[i] = static_cast<float>(deviceProps[i].multiProcessorCount);
        totalWeight += weights[i];
    }

    // Normalize and distribute
    int assignedWork = 0;
    for (int i = 0; i < deviceCount; i++) {
        distribution[i] = static_cast<int>((weights[i] / totalWeight) * totalWork);
        assignedWork += distribution[i];
    }

    // Assign remaining work to most capable device
    int remaining = totalWork - assignedWork;
    if (remaining > 0) {
        int bestDevice = std::distance(weights.begin(),
                                      std::max_element(weights.begin(), weights.end()));
        distribution[bestDevice] += remaining;
    }

    return distribution;
}

void MultiGPUManager::synchronizeAll() const {
    for (int i = 0; i < deviceCount; i++) {
        cudaSetDevice(i);
        cudaStreamSynchronize(streams[i]);
    }
}

void MultiGPUManager::printTopology() const {
    printf("\n=== Multi-GPU Topology ===\n");
    printf("Number of GPUs: %d\n\n", deviceCount);

    printf("Peer Access Matrix:\n");
    printf("     ");
    for (int j = 0; j < deviceCount; j++) {
        printf("GPU%d ", j);
    }
    printf("\n");

    for (int i = 0; i < deviceCount; i++) {
        printf("GPU%d ", i);
        for (int j = 0; j < deviceCount; j++) {
            if (i == j) {
                printf(" -   ");
            } else {
                printf(" %s  ", peerAccessMatrix[i][j] ? "YES" : "NO ");
            }
        }
        printf("\n");
    }
    printf("\n");
}

cudaStream_t MultiGPUManager::getStream(int device) const {
    if (device < 0 || device >= deviceCount) {
        return nullptr;
    }
    return streams[device];
}

const cudaDeviceProp& MultiGPUManager::getDeviceProperties(int device) const {
    return deviceProps[device];
}
