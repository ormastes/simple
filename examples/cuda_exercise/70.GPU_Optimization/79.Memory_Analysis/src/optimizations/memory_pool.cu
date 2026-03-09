/**
 * @file memory_pool.cu
 * @brief Free-list GPU memory pool allocator implementation.
 *
 * Implements a simple memory pool that pre-allocates a large chunk of GPU
 * memory and serves allocation requests from a free list. This avoids the
 * overhead of repeated cudaMalloc/cudaFree calls in tight loops.
 */
#include "optimizations/memory_pool.h"
#include <cuda_runtime.h>
#include <cstdio>
#include <algorithm>

namespace opt79 {

MemoryPool::MemoryPool(size_t total_bytes)
    : total_bytes_(total_bytes), base_ptr_(nullptr) {}

MemoryPool::~MemoryPool() { destroy(); }

bool MemoryPool::init() {
    if (base_ptr_) return true;  // Already initialized

    cudaError_t err = cudaMalloc(&base_ptr_, total_bytes_);
    if (err != cudaSuccess) {
        fprintf(stderr, "MemoryPool: cudaMalloc(%zu) failed: %s\n",
                total_bytes_, cudaGetErrorString(err));
        return false;
    }

    // Start with one big free block
    blocks_.clear();
    PoolBlock b;
    b.offset = 0;
    b.size = total_bytes_;
    b.in_use = false;
    blocks_.push_back(b);
    return true;
}

void* MemoryPool::allocate(size_t size) {
    // Round up to 256-byte alignment
    size = (size + 255) & ~(size_t)255;

    // First-fit search using index to avoid iterator invalidation
    for (size_t i = 0; i < blocks_.size(); i++) {
        if (!blocks_[i].in_use && blocks_[i].size >= size) {
            // Split block if significantly larger
            if (blocks_[i].size > size + 256) {
                PoolBlock remainder;
                remainder.offset = blocks_[i].offset + size;
                remainder.size = blocks_[i].size - size;
                remainder.in_use = false;
                blocks_[i].size = size;
                blocks_.insert(blocks_.begin() + (int)i + 1, remainder);
            }
            blocks_[i].in_use = true;
            return static_cast<char*>(base_ptr_) + blocks_[i].offset;
        }
    }
    return nullptr;  // Out of pool memory
}

void MemoryPool::deallocate(void* ptr) {
    if (!ptr || !base_ptr_) return;

    size_t offset = static_cast<char*>(ptr) - static_cast<char*>(base_ptr_);

    for (auto& b : blocks_) {
        if (b.offset == offset && b.in_use) {
            b.in_use = false;
            coalesce();
            return;
        }
    }
    fprintf(stderr, "MemoryPool::deallocate: pointer not found in pool\n");
}

void MemoryPool::destroy() {
    if (base_ptr_) {
        cudaFree(base_ptr_);
        base_ptr_ = nullptr;
    }
    blocks_.clear();
}

size_t MemoryPool::used_bytes() const {
    size_t used = 0;
    for (const auto& b : blocks_) {
        if (b.in_use) used += b.size;
    }
    return used;
}

size_t MemoryPool::num_free_blocks() const {
    size_t count = 0;
    for (const auto& b : blocks_) {
        if (!b.in_use) count++;
    }
    return count;
}

void MemoryPool::print_state() const {
    printf("=== Memory Pool ===\n");
    printf("Total: %zu bytes, Used: %zu bytes, Free blocks: %zu\n",
           total_bytes_, used_bytes(), num_free_blocks());
    for (const auto& b : blocks_) {
        printf("  [%8zu +%8zu] %s\n", b.offset, b.size,
               b.in_use ? "IN USE" : "FREE");
    }
    printf("===================\n");
}

void MemoryPool::coalesce() {
    for (size_t i = 0; i + 1 < blocks_.size(); ) {
        if (!blocks_[i].in_use && !blocks_[i + 1].in_use) {
            blocks_[i].size += blocks_[i + 1].size;
            blocks_.erase(blocks_.begin() + i + 1);
        } else {
            ++i;
        }
    }
}

}  // namespace opt79
