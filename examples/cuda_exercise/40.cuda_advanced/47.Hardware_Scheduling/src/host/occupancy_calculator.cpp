// occupancy_calculator.cpp - CUDA occupancy analysis and optimization

#include <cuda_runtime.h>
#include <cstdio>
#include <algorithm>
#include <climits>

struct OccupancyResult {
    int blocksPerSM;
    int activeWarps;
    int activeThreads;
    float occupancyPercent;
    int limitingFactor;  // 0=threads, 1=blocks, 2=sharedMem, 3=registers
};

struct OccupancyCalculator {
    cudaDeviceProp deviceProps;
    int deviceId;

    OccupancyCalculator(int device = 0) : deviceId(device) {
        cudaGetDeviceProperties(&deviceProps, device);
    }

    void printDeviceInfo() const {
        printf("GPU Scheduling Information:\n");
        printf("  Device: %s\n", deviceProps.name);
        printf("  Streaming Multiprocessors: %d\n", deviceProps.multiProcessorCount);
        printf("  Max threads per SM: %d\n", deviceProps.maxThreadsPerMultiProcessor);
        printf("  Max blocks per SM: %d\n", deviceProps.maxBlocksPerMultiProcessor);
        printf("  Warp size: %d\n", deviceProps.warpSize);
        printf("  Max warps per SM: %d\n", deviceProps.maxThreadsPerMultiProcessor / deviceProps.warpSize);
        printf("  Max shared memory per SM: %zu bytes\n", deviceProps.sharedMemPerMultiprocessor);
        printf("  Max registers per SM: %d\n", deviceProps.regsPerMultiprocessor);
    }

    OccupancyResult calculateOccupancy(int blockSize, int sharedMemPerBlock, int regsPerThread) const {
        OccupancyResult result;

        // Calculate maximum blocks limited by each resource
        int maxBlocksByThreads = deviceProps.maxThreadsPerMultiProcessor / blockSize;
        int maxBlocksByBlocks = deviceProps.maxBlocksPerMultiProcessor;
        int maxBlocksBySharedMem = (sharedMemPerBlock > 0) ?
            static_cast<int>(deviceProps.sharedMemPerMultiprocessor / sharedMemPerBlock) : INT_MAX;
        int maxBlocksByRegs = (regsPerThread > 0) ?
            deviceProps.regsPerMultiprocessor / (blockSize * regsPerThread) : INT_MAX;

        // Find the limiting factor
        result.blocksPerSM = maxBlocksByThreads;
        result.limitingFactor = 0;

        if (maxBlocksByBlocks < result.blocksPerSM) {
            result.blocksPerSM = maxBlocksByBlocks;
            result.limitingFactor = 1;
        }
        if (maxBlocksBySharedMem < result.blocksPerSM) {
            result.blocksPerSM = maxBlocksBySharedMem;
            result.limitingFactor = 2;
        }
        if (maxBlocksByRegs < result.blocksPerSM) {
            result.blocksPerSM = maxBlocksByRegs;
            result.limitingFactor = 3;
        }

        // Calculate occupancy metrics
        result.activeThreads = result.blocksPerSM * blockSize;
        result.activeWarps = result.activeThreads / deviceProps.warpSize;
        result.occupancyPercent = (float)result.activeThreads / deviceProps.maxThreadsPerMultiProcessor * 100.0f;

        return result;
    }

    void printOccupancyAnalysis(int blockSize, int sharedMemPerBlock, int regsPerThread) const {
        printf("\nOccupancy Analysis:\n");
        printf("  Block size: %d threads\n", blockSize);
        printf("  Shared memory per block: %d bytes\n", sharedMemPerBlock);
        printf("  Registers per thread: %d\n", regsPerThread);

        OccupancyResult result = calculateOccupancy(blockSize, sharedMemPerBlock, regsPerThread);

        // Calculate limits for debugging
        int maxBlocksByThreads = deviceProps.maxThreadsPerMultiProcessor / blockSize;
        int maxBlocksByBlocks = deviceProps.maxBlocksPerMultiProcessor;
        int maxBlocksBySharedMem = (sharedMemPerBlock > 0) ?
            static_cast<int>(deviceProps.sharedMemPerMultiprocessor / sharedMemPerBlock) : INT_MAX;
        int maxBlocksByRegs = (regsPerThread > 0) ?
            deviceProps.regsPerMultiprocessor / (blockSize * regsPerThread) : INT_MAX;

        printf("  Limiting factors:\n");
        printf("    By threads: %d blocks%s\n", maxBlocksByThreads,
               result.limitingFactor == 0 ? " [LIMITING]" : "");
        printf("    By blocks: %d blocks%s\n", maxBlocksByBlocks,
               result.limitingFactor == 1 ? " [LIMITING]" : "");
        printf("    By shared memory: %d blocks%s\n", maxBlocksBySharedMem,
               result.limitingFactor == 2 ? " [LIMITING]" : "");
        printf("    By registers: %d blocks%s\n", maxBlocksByRegs,
               result.limitingFactor == 3 ? " [LIMITING]" : "");
        printf("  Actual blocks per SM: %d\n", result.blocksPerSM);
        printf("  Active warps per SM: %d\n", result.activeWarps);
        printf("  Theoretical occupancy: %.1f%%\n", result.occupancyPercent);
    }

    int getOptimalBlockSize(size_t sharedMemPerBlock) const {
        // Try common block sizes and find the one with best occupancy
        int sizes[] = {32, 64, 96, 128, 160, 192, 224, 256, 288, 320, 352, 384, 416, 448, 480, 512, 768, 1024};
        int bestSize = 256;
        float bestOccupancy = 0.0f;

        for (int size : sizes) {
            if (size > deviceProps.maxThreadsPerBlock) break;

            OccupancyResult result = calculateOccupancy(size, sharedMemPerBlock, 0);
            if (result.occupancyPercent > bestOccupancy) {
                bestOccupancy = result.occupancyPercent;
                bestSize = size;
            }
        }

        return bestSize;
    }
};

// Helper function to get device properties
cudaDeviceProp getDeviceProperties(int device = 0) {
    cudaDeviceProp props;
    cudaGetDeviceProperties(&props, device);
    return props;
}

// Helper function to calculate grid size based on problem size
int calculateGridSize(int n, int blockSize) {
    return (n + blockSize - 1) / blockSize;
}
