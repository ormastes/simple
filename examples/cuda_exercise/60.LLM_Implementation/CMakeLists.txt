# 60.LLM_Implementation - Large Language Model from Scratch
#
# This category implements a complete LLM based on "LLMs from Scratch" by Sebastian Raschka
# with extensions for DeepSeek R1 compatibility and NVMe-based expert loading.
#
# Modules (61-69):
# - 61: Foundation (Tokenization & Embeddings)
# - 62: Attention Mechanisms
# - 63: Transformer Blocks
# - 64: GPT Architecture
# - 65: Training Infrastructure
# - 66: Model Loading & Inference
# - 67: DeepSeek R1 Adaptation
# - 68: MoE Implementation
# - 69: MoE + NVMe Integration & Complete LLM System

# Module 61: Foundation - Tokenization and Embeddings
# NOTE: Module 61 has incomplete source files (only v1 tokenizer + token_embedding)
# Uncomment when remaining implementations are added
# add_subdirectory(61.Foundation_Tokenization_Embeddings)

# Module 62: Attention Mechanisms
add_subdirectory(62.Attention_Mechanisms)

# Module 63: Transformer Blocks
add_subdirectory(63.Transformer_Blocks)

# Module 64: GPT Architecture
add_subdirectory(64.GPT_Architecture)

# Module 65: Training Infrastructure
add_subdirectory(65.Training_Infrastructure)

# Module 66: Model Loading & Inference
add_subdirectory(66.Model_Loading_Inference)

# Module 67: DeepSeek R1 Adaptation
add_subdirectory(67.DeepSeek_R1_Adaptation)

# Module 68: MoE Implementation
add_subdirectory(68.MoE_Implementation)

# Module 69: MoE + NVMe Complete System
add_subdirectory(69.MoE_NVMe_Complete_System)
