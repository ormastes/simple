# Module 64: GPT Architecture

## Overview

This module implements the complete GPT (Generative Pre-trained Transformer) architecture, combining token/position embeddings from Module 61, attention mechanisms from Module 62, and transformer blocks from Module 63 into a unified language model capable of next-token prediction and text generation.

Based on "LLMs from Scratch" by Sebastian Raschka (Chapters 4-5).

## Architecture

The module is organized into the following components:

### Configuration (common/)
- **GPTConfig**: Model hyperparameters (dimensions, layers, heads)
- **Factory functions**: `gpt2_small()`, `gpt2_medium()`, `gpt2_large()`, `gpt_tiny()`
- **count_parameters()**: Compute total learnable parameter count

### Model (common/, kernels/)
- **GPTModel**: Complete GPT model with allocation, forward pass, and deallocation
- **GPTModelWeights**: All weight tensors (embeddings, transformer layers, final norm)
- **Weight tying**: LM head shares weights with token embeddings

### Sampling (common/, kernels/)
- **gpu_top_k_sampling()**: Keep top-k logits, softmax, sample
- **gpu_top_p_sampling()**: Nucleus sampling with cumulative probability threshold

### Generation (common/, kernels/)
- **generate()**: Autoregressive text generation loop

## Key APIs

### Model Operations
- @ref GPTModel::allocate() - Allocate and initialize all model weights
- @ref GPTModel::forward() - Forward pass: token IDs to logits
- @ref GPTModel::deallocate() - Free all GPU memory

### Sampling
- @ref gpu_top_k_sampling() - Sample from top-k candidates
- @ref gpu_top_p_sampling() - Sample from nucleus (top-p) set
- @ref generate() - Complete autoregressive generation

## Usage Example

```cpp
#include "common/gpt_model.h"
#include "common/text_generator.h"

// Create and allocate model
GPTModel model;
model.config = gpt_tiny();  // Use tiny config for testing
model.allocate();

// Forward pass
float* d_logits;
int* d_input_ids;
// ... allocate and fill input ...
model.forward(d_logits, d_input_ids, batch_size, seq_len);

// Generate text
SamplingConfig sampling;
sampling.top_k = 50;
sampling.temperature = 0.8f;
sampling.max_new_tokens = 100;

int* d_output_ids;
// ... allocate output buffer ...
generate(d_output_ids, model, d_prompt, prompt_len, sampling);

model.deallocate();
```

## Testing

Unit tests are available in `test/unit/kernels/`:
- `test_gpt_model.cu`: Model allocation, parameter counting, forward pass correctness
- `test_sampling.cu`: Top-k and top-p sampling validity and distribution
- `test_text_generator.cu`: Generation loop output length and token validity

## References

- [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) - Base reference
- [Language Models are Unsupervised Multitask Learners](https://cdn.openai.com/better-language-models/language_models_are_unsupervised_multitask_learners.pdf) - GPT-2 paper
- [Attention Is All You Need](https://arxiv.org/abs/1706.03762) - Transformer architecture
