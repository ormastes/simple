/**
 * @file memory_profiler.h
 * @brief GPU memory tracking and profiling with labeled allocations.
 */

#pragma once
#include <cuda_runtime.h>
#include <vector>
#include <cstddef>

namespace opt79 {

/// @brief Record of a single GPU memory allocation
struct Allocation {
    void* ptr;          ///< Device pointer
    size_t size;        ///< Allocation size in bytes
    char label[64];     ///< Human-readable label
};

/**
 * @brief GPU memory allocation tracker.
 *
 * Wraps cudaMalloc/cudaFree to maintain a ledger of active allocations,
 * compute current and peak memory usage, and print diagnostic reports.
 *
 * @code
 * MemoryTracker tracker;
 * void* p = tracker.tracked_malloc(1024, "weights");
 * tracker.print_report();
 * tracker.tracked_free(p);
 * @endcode
 */
struct MemoryTracker {
    std::vector<Allocation> allocations;  ///< Active allocations
    size_t current_usage = 0;             ///< Current total bytes allocated
    size_t peak_usage = 0;                ///< Peak total bytes allocated

    /// @brief Allocate GPU memory with tracking
    void* tracked_malloc(size_t size, const char* label);

    /// @brief Free GPU memory and remove from tracker
    void tracked_free(void* ptr);

    /// @brief Print a summary report of all active allocations
    void print_report() const;

    /// @brief Check for memory leaks (returns number of active allocations)
    size_t check_leaks() const;

    /// @brief Free all tracked allocations
    void free_all();
};

}  // namespace opt79
