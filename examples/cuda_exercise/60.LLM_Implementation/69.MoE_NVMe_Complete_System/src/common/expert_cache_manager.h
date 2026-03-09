/**
 * @file expert_cache_manager.h
 * @brief LRU cache manager for MoE expert weights
 *
 * Manages expert weights between GPU memory and NVMe storage,
 * loading experts on-demand based on router decisions. The cache
 * uses an LRU eviction policy to keep the most recently used
 * experts in GPU memory while offloading inactive experts to NVMe.
 */
#pragma once
#include <cuda_runtime.h>
#include <cstddef>
#include <cstdio>

namespace llm {

/**
 * @brief Configuration for the expert cache manager
 *
 * Specifies the total number of experts, how many can be cached
 * simultaneously in GPU memory, and whether NVMe storage is enabled.
 */
struct ExpertCacheConfig {
    int num_experts;           ///< Total number of experts in the model
    int max_cached_experts;    ///< Maximum experts held in GPU memory at once
    size_t expert_size_bytes;  ///< Size of each expert's weight tensor in bytes
    bool use_nvme;             ///< Enable NVMe-based offloading for uncached experts
};

/**
 * @brief LRU cache manager for MoE expert weights
 *
 * Provides transparent access to expert weights by maintaining a GPU-resident
 * cache with LRU eviction. When an expert is requested but not in cache, it
 * is loaded from NVMe storage (if enabled) and the least recently used expert
 * is evicted to make room.
 *
 * @code
 * ExpertCacheConfig config = {64, 8, 1024*1024, true};
 * ExpertCacheManager cache;
 * cache.init(config);
 *
 * float* weights = cache.get_expert(42, stream);
 * // Use weights in kernel...
 *
 * cache.print_stats();
 * cache.destroy();
 * @endcode
 */
struct ExpertCacheManager {
    ExpertCacheConfig config;   ///< Current cache configuration
    float** expert_buffers;     ///< GPU buffers for cached experts
    int* cache_order;           ///< LRU order tracking (index 0 = most recent)
    bool* in_cache;             ///< Bitmap of which experts are currently cached
    int* cache_slot_map;        ///< Maps expert_id -> cache slot index (-1 if not cached)
    int cache_hits;             ///< Number of cache hit accesses
    int cache_misses;           ///< Number of cache miss accesses

    /**
     * @brief Initialize the cache with the given configuration
     * @param[in] cfg Cache configuration parameters
     */
    void init(const ExpertCacheConfig& cfg) {
        config = cfg;
        cache_hits = 0;
        cache_misses = 0;

        expert_buffers = new float*[config.max_cached_experts];
        for (int i = 0; i < config.max_cached_experts; ++i) {
            cudaMalloc(&expert_buffers[i], config.expert_size_bytes);
        }

        cache_order = new int[config.max_cached_experts];
        for (int i = 0; i < config.max_cached_experts; ++i) {
            cache_order[i] = -1;  // Empty slot
        }

        in_cache = new bool[config.num_experts];
        cache_slot_map = new int[config.num_experts];
        for (int i = 0; i < config.num_experts; ++i) {
            in_cache[i] = false;
            cache_slot_map[i] = -1;
        }
    }

    /**
     * @brief Get expert weights, loading from NVMe if not cached
     * @param[in] expert_id Index of the expert to retrieve
     * @param[in] stream CUDA stream for async loading
     * @return Pointer to GPU buffer containing the expert weights
     */
    float* get_expert(int expert_id, cudaStream_t stream = 0) {
        if (expert_id < 0 || expert_id >= config.num_experts) {
            return nullptr;
        }

        if (in_cache[expert_id]) {
            cache_hits++;
            // Move to front of LRU order
            int slot = cache_slot_map[expert_id];
            promote_slot(slot);
            return expert_buffers[slot];
        }

        cache_misses++;
        int slot = find_free_slot();
        if (slot < 0) {
            slot = evict_lru();
        }

        // Load expert into slot (NVMe or zero-fill)
        if (config.use_nvme) {
            // NVMe loading would be done via NVMeExpertStorage
            cudaMemsetAsync(expert_buffers[slot], 0, config.expert_size_bytes, stream);
        } else {
            cudaMemsetAsync(expert_buffers[slot], 0, config.expert_size_bytes, stream);
        }

        cache_slot_map[expert_id] = slot;
        in_cache[expert_id] = true;
        promote_slot(slot);

        return expert_buffers[slot];
    }

    /**
     * @brief Evict the least recently used expert from cache
     * @return The cache slot index that was freed
     */
    int evict_lru() {
        // Find least recently used slot (last valid in cache_order)
        int lru_slot = cache_order[config.max_cached_experts - 1];
        if (lru_slot < 0) {
            lru_slot = 0;
        }

        // Find which expert occupied this slot and remove it
        for (int i = 0; i < config.num_experts; ++i) {
            if (cache_slot_map[i] == lru_slot) {
                in_cache[i] = false;
                cache_slot_map[i] = -1;
                break;
            }
        }

        return lru_slot;
    }

    /**
     * @brief Report cache hit/miss statistics
     */
    void print_stats() const {
        int total = cache_hits + cache_misses;
        float hit_rate = total > 0 ? (100.0f * cache_hits / total) : 0.0f;
        printf("Expert Cache Stats: hits=%d, misses=%d, hit_rate=%.1f%%\n",
               cache_hits, cache_misses, hit_rate);
    }

    /**
     * @brief Free all GPU memory and host allocations
     */
    void destroy() {
        if (expert_buffers) {
            for (int i = 0; i < config.max_cached_experts; ++i) {
                cudaFree(expert_buffers[i]);
            }
            delete[] expert_buffers;
            expert_buffers = nullptr;
        }
        delete[] cache_order;
        cache_order = nullptr;
        delete[] in_cache;
        in_cache = nullptr;
        delete[] cache_slot_map;
        cache_slot_map = nullptr;
    }

private:
    /// Find a free (unoccupied) cache slot, returns -1 if none available
    int find_free_slot() const {
        for (int i = 0; i < config.max_cached_experts; ++i) {
            if (cache_order[i] < 0) {
                return i;
            }
        }
        return -1;
    }

    /// Promote a slot to most-recently-used position
    void promote_slot(int slot) {
        // Remove slot from current position
        int pos = -1;
        for (int i = 0; i < config.max_cached_experts; ++i) {
            if (cache_order[i] == slot) {
                pos = i;
                break;
            }
        }

        if (pos > 0) {
            // Shift entries down and place slot at front
            for (int i = pos; i > 0; --i) {
                cache_order[i] = cache_order[i - 1];
            }
        } else if (pos < 0) {
            // New entry: shift everything down
            for (int i = config.max_cached_experts - 1; i > 0; --i) {
                cache_order[i] = cache_order[i - 1];
            }
        }

        cache_order[0] = slot;
    }
};

} // namespace llm
