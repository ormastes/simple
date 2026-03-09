/**
 * @file memory_profiler.cu
 * @brief GPU memory tracking and profiling implementation.
 *
 * Provides a MemoryTracker class that wraps cudaMalloc/cudaFree to record
 * allocations with labels, track current and peak usage, and generate
 * summary reports. Useful for identifying memory hotspots and leaks.
 */
#include "profiling/memory_profiler.h"
#include <cuda_runtime.h>
#include <cstdio>
#include <cstring>

namespace opt79 {

void* MemoryTracker::tracked_malloc(size_t size, const char* label) {
    void* ptr = nullptr;
    cudaError_t err = cudaMalloc(&ptr, size);
    if (err != cudaSuccess || ptr == nullptr) {
        fprintf(stderr, "tracked_malloc failed for '%s' (%zu bytes): %s\n",
                label, size, cudaGetErrorString(err));
        return nullptr;
    }
    Allocation a;
    a.ptr = ptr;
    a.size = size;
    strncpy(a.label, label, 63);
    a.label[63] = '\0';
    allocations.push_back(a);
    current_usage += size;
    if (current_usage > peak_usage) peak_usage = current_usage;
    return ptr;
}

void MemoryTracker::tracked_free(void* ptr) {
    for (auto it = allocations.begin(); it != allocations.end(); ++it) {
        if (it->ptr == ptr) {
            current_usage -= it->size;
            cudaFree(ptr);
            allocations.erase(it);
            return;
        }
    }
    fprintf(stderr, "tracked_free: pointer %p not found in tracker\n", ptr);
}

void MemoryTracker::print_report() const {
    printf("=== Memory Report ===\n");
    printf("Active allocations: %zu\n", allocations.size());
    printf("Current usage:      %zu bytes (%.2f MB)\n",
           current_usage, current_usage / (1024.0 * 1024.0));
    printf("Peak usage:         %zu bytes (%.2f MB)\n",
           peak_usage, peak_usage / (1024.0 * 1024.0));
    if (!allocations.empty()) {
        printf("\nActive allocations:\n");
        for (const auto& a : allocations) {
            printf("  [%p] %zu bytes - %s\n", a.ptr, a.size, a.label);
        }
    }
    printf("=====================\n");
}

size_t MemoryTracker::check_leaks() const {
    if (!allocations.empty()) {
        printf("WARNING: %zu allocations still active (potential leaks):\n",
               allocations.size());
        for (const auto& a : allocations) {
            printf("  LEAK: [%p] %zu bytes - %s\n", a.ptr, a.size, a.label);
        }
    }
    return allocations.size();
}

void MemoryTracker::free_all() {
    for (auto& a : allocations) {
        cudaFree(a.ptr);
    }
    allocations.clear();
    current_usage = 0;
}

}  // namespace opt79
