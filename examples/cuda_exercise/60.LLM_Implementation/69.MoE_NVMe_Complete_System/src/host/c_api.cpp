/**
 * @file c_api.cpp
 * @brief Implementation of the C API for the complete LLM system
 *
 * Bridges the C API declared in llm_api.h to the underlying C++/CUDA
 * model components, managing model lifecycle and autoregressive generation.
 */

#include "common/llm_api.h"
#include "common/expert_cache_manager.h"
#include "common/nvme_expert_storage.h"
#include <cstdio>
#include <cstdlib>
#include <cstring>

/// Internal model state hidden behind the opaque LLMModel handle
struct LLMModelInternal {
    int vocab_size;
    int max_seq_len;
    int d_model;
    int num_layers;
    int num_experts;
    long long num_parameters;

    llm::ExpertCacheManager expert_cache;
    llm::NVMeExpertStorage expert_storage;

    bool initialized;
};

LLMModel llm_create_model(const char* config_path) {
    if (!config_path) {
        fprintf(stderr, "llm_create_model: config_path is NULL\n");
        return nullptr;
    }

    auto* model = new LLMModelInternal();
    model->initialized = false;

    // Default configuration (would be loaded from config_path in production)
    model->vocab_size = 50257;
    model->max_seq_len = 1024;
    model->d_model = 768;
    model->num_layers = 12;
    model->num_experts = 8;
    model->num_parameters = 0;

    // Parse config file if it exists
    FILE* f = fopen(config_path, "r");
    if (f) {
        // Simple key=value config parsing
        char line[256];
        while (fgets(line, sizeof(line), f)) {
            int val;
            if (sscanf(line, "vocab_size=%d", &val) == 1) model->vocab_size = val;
            else if (sscanf(line, "max_seq_len=%d", &val) == 1) model->max_seq_len = val;
            else if (sscanf(line, "d_model=%d", &val) == 1) model->d_model = val;
            else if (sscanf(line, "num_layers=%d", &val) == 1) model->num_layers = val;
            else if (sscanf(line, "num_experts=%d", &val) == 1) model->num_experts = val;
        }
        fclose(f);
    }

    // Calculate approximate parameter count
    // Embedding: vocab_size * d_model
    // Per layer: 4 * d_model^2 (attention) + num_experts * 2 * d_model * 4*d_model (MoE FFN)
    long long embed_params = (long long)model->vocab_size * model->d_model;
    long long attn_params = 4LL * model->d_model * model->d_model;
    long long expert_params = (long long)model->num_experts * 2 * model->d_model * (4 * model->d_model);
    model->num_parameters = embed_params + model->num_layers * (attn_params + expert_params);

    // Initialize expert cache
    size_t expert_weight_size = (size_t)(2 * model->d_model * 4 * model->d_model) * sizeof(float);
    llm::ExpertCacheConfig cache_cfg;
    cache_cfg.num_experts = model->num_experts;
    cache_cfg.max_cached_experts = (model->num_experts < 4) ? model->num_experts : 4;
    cache_cfg.expert_size_bytes = expert_weight_size;
    cache_cfg.use_nvme = false;  // Disabled by default; enable via config
    model->expert_cache.init(cache_cfg);

    model->initialized = true;
    return static_cast<LLMModel>(model);
}

int llm_generate(LLMModel model, const int* input_ids, int input_len,
                int* output_ids, int max_output_len) {
    if (!model || !input_ids || !output_ids || input_len <= 0 || max_output_len <= 0) {
        return -1;
    }

    auto* m = static_cast<LLMModelInternal*>(model);
    if (!m->initialized) {
        return -1;
    }

    // Autoregressive generation loop (placeholder implementation)
    // In a full system this would:
    // 1. Encode input through embedding + transformer layers
    // 2. Run MoE routing at each layer
    // 3. Load required experts via cache manager
    // 4. Compute output logits
    // 5. Sample next token
    // 6. Repeat until EOS or max_output_len

    int generated = 0;
    for (int i = 0; i < max_output_len; ++i) {
        // Placeholder: generate sequential token IDs (wrapping at vocab_size)
        int last_token = (i == 0 && input_len > 0) ? input_ids[input_len - 1] : output_ids[i - 1];
        int next_token = (last_token + 1) % m->vocab_size;

        // Check for EOS token (token ID 0 is a simple sentinel)
        if (next_token == 0 && i > 0) {
            break;
        }

        output_ids[i] = next_token;
        generated++;
    }

    return generated;
}

void llm_destroy_model(LLMModel model) {
    if (!model) {
        return;
    }

    auto* m = static_cast<LLMModelInternal*>(model);
    m->expert_cache.destroy();
    m->expert_storage.destroy();
    delete m;
}

int llm_get_vocab_size(LLMModel model) {
    if (!model) return -1;
    return static_cast<LLMModelInternal*>(model)->vocab_size;
}

int llm_get_max_seq_len(LLMModel model) {
    if (!model) return -1;
    return static_cast<LLMModelInternal*>(model)->max_seq_len;
}

long long llm_get_num_parameters(LLMModel model) {
    if (!model) return -1;
    return static_cast<LLMModelInternal*>(model)->num_parameters;
}
