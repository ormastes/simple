/**
 * @file moe_transformer.h
 * @brief Full transformer with MoE FFN layers
 *
 * Defines the configuration and forward pass for a transformer model that
 * uses Mixture-of-Experts for its feed-forward layers. In DeepSeek R1,
 * some layers use dense FFN while others use MoE FFN. This interface
 * supports both configurations within the same model.
 */

#pragma once

#include <cuda_runtime.h>
#include "moe_layer.h"
#include "common/deepseek_config.h"

namespace llm {

/**
 * @brief MoE transformer layer configuration
 *
 * Extends the DeepSeek config with per-layer MoE settings. In DeepSeek R1,
 * the first few layers use dense FFN and the remaining layers use MoE.
 */
struct MoETransformerConfig {
    DeepSeekConfig base;           ///< Base model configuration
    int first_moe_layer;           ///< First layer index that uses MoE (0-indexed)
    float aux_loss_weight;         ///< Weight for load balancing loss

    /**
     * @brief Construct MoE transformer configuration
     *
     * @param base             Base DeepSeek model config
     * @param first_moe_layer  First MoE layer index (default: 1, layer 0 is dense)
     * @param aux_loss_weight  Auxiliary loss weight (default: 0.01)
     */
    MoETransformerConfig(const DeepSeekConfig& base = DeepSeekConfig(),
                         int first_moe_layer = 1,
                         float aux_loss_weight = 0.01f)
        : base(base), first_moe_layer(first_moe_layer),
          aux_loss_weight(aux_loss_weight) {}
};

/**
 * @brief Check if a given layer should use MoE FFN
 *
 * @param[in] layer_idx      Layer index (0-based)
 * @param[in] config         Transformer configuration
 * @return true if this layer uses MoE, false for dense FFN
 */
inline bool is_moe_layer(int layer_idx, const MoETransformerConfig& config) {
    return layer_idx >= config.first_moe_layer && config.base.num_experts > 0;
}

} // namespace llm
