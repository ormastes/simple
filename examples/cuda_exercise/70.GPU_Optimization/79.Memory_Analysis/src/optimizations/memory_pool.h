/**
 * @file memory_pool.h
 * @brief Free-list GPU memory pool allocator to reduce cudaMalloc/cudaFree overhead.
 */

#pragma once
#include <cuda_runtime.h>
#include <cstddef>
#include <vector>

namespace opt79 {

/// @brief A block in the pool's free/active list
struct PoolBlock {
    size_t offset;  ///< Offset from pool base in bytes
    size_t size;    ///< Block size in bytes
    bool in_use;    ///< Whether this block is currently allocated
};

/**
 * @brief Simple free-list GPU memory pool.
 *
 * Pre-allocates a contiguous GPU memory region and manages sub-allocations
 * via a free-list. Supports allocation and deallocation with first-fit
 * strategy and automatic coalescing of adjacent free blocks.
 *
 * @code
 * MemoryPool pool(64 * 1024 * 1024);  // 64 MB pool
 * pool.init();
 * void* p = pool.allocate(1024);
 * pool.deallocate(p);
 * pool.destroy();
 * @endcode
 *
 * @note Allocations are aligned to 256-byte boundaries
 */
class MemoryPool {
public:
    /// @brief Construct with given capacity (does not allocate until init())
    explicit MemoryPool(size_t total_bytes);
    ~MemoryPool();

    // Non-copyable
    MemoryPool(const MemoryPool&) = delete;
    MemoryPool& operator=(const MemoryPool&) = delete;

    /// @brief Allocate the underlying GPU buffer
    bool init();

    /// @brief Allocate from the pool (first-fit, 256-byte aligned)
    void* allocate(size_t size);

    /// @brief Return memory to the pool
    void deallocate(void* ptr);

    /// @brief Free the underlying GPU buffer
    void destroy();

    /// @brief Get total pool capacity in bytes
    size_t total_bytes() const { return total_bytes_; }

    /// @brief Get currently allocated bytes
    size_t used_bytes() const;

    /// @brief Get number of free blocks
    size_t num_free_blocks() const;

    /// @brief Print pool state to stdout
    void print_state() const;

private:
    void coalesce();

    size_t total_bytes_;
    void* base_ptr_;
    std::vector<PoolBlock> blocks_;
};

}  // namespace opt79
