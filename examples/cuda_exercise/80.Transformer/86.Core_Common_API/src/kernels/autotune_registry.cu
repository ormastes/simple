/**
 * @file autotune_registry.cu
 * @brief Runtime autotuning registry for GEMM kernel selection
 */
#include "common/autotune_registry.cuh"
#include <unordered_map>
#include <mutex>

namespace transformer {

namespace {
    struct ConfigKey {
        int M, N, K, sm;
        bool operator==(const ConfigKey& o) const {
            return M == o.M && N == o.N && K == o.K && sm == o.sm;
        }
    };

    struct ConfigKeyHash {
        size_t operator()(const ConfigKey& k) const {
            size_t h = std::hash<int>()(k.M);
            h ^= std::hash<int>()(k.N) << 1;
            h ^= std::hash<int>()(k.K) << 2;
            h ^= std::hash<int>()(k.sm) << 3;
            return h;
        }
    };

    std::unordered_map<ConfigKey, GemmConfig, ConfigKeyHash> cache;
    std::mutex cache_mutex;
}

GemmConfig get_best_config(int M, int N, int K, int sm) {
    std::lock_guard<std::mutex> lock(cache_mutex);
    ConfigKey key{M, N, K, sm};
    auto it = cache.find(key);
    if (it != cache.end()) {
        return it->second;
    }
    // Return default config
    GemmConfig def;
    def.M = M; def.N = N; def.K = K;
    def.sm_version = sm;
    if (sm >= 70) {
        def.kernel = GemmKernel::WMMA_FP16;
        def.tile_m = 16; def.tile_n = 16; def.tile_k = 16;
    } else {
        def.kernel = GemmKernel::SIMT_FP32;
        def.tile_m = 32; def.tile_n = 32; def.tile_k = 8;
    }
    return def;
}

void register_config(const GemmConfig& config) {
    std::lock_guard<std::mutex> lock(cache_mutex);
    ConfigKey key{config.M, config.N, config.K, config.sm_version};
    cache[key] = config;
}

void clear_autotune_cache() {
    std::lock_guard<std::mutex> lock(cache_mutex);
    cache.clear();
}

} // namespace transformer
