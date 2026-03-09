# Module 66: Model Loading and Inference

## Overview

This module implements the infrastructure for loading trained model weights and running efficient inference. It provides binary checkpoint serialization, HuggingFace SafeTensors format parsing, a KV cache for incremental attention computation, and beam search decoding for high-quality text generation.

## Architecture

### Checkpoint Persistence (common/, host/)
- **CheckpointHeader**: Binary format with magic number and tensor metadata
- **save_checkpoint()**: Serialize model weights from device to binary file
- **load_checkpoint()**: Deserialize binary checkpoint back to device memory
- **get_checkpoint_param_count()**: Query parameter count without loading data

### SafeTensors Loading (common/, host/)
- **SafeTensorsHeader**: JSON header parser for HuggingFace format
- **parse_safetensors()**: Parse the 8-byte + JSON header structure
- **load_safetensor_data()**: Load individual tensors with dtype conversion (F16/BF16 to F32)
- **mmap_safetensors()**: Memory-mapped file access for zero-copy loading

### KV Cache (common/, kernels/)
- **KVCache**: Per-layer key/value storage for incremental decoding
- **kv_cache_append_kernel**: GPU kernel to append new tokens to cache
- **kv_cache_rotate_kernel**: GPU kernel for sliding window cache rotation

### Beam Search (common/, host/)
- **InferenceEngine**: Complete inference pipeline with KV cache management
- **beam_search()**: Maintain top-k hypotheses with length-normalized scoring
- **generate_with_cache()**: Autoregressive generation with KV cache

## Key APIs

- @ref llm::save_checkpoint() - Save weights to binary file
- @ref llm::load_checkpoint() - Load weights from binary file
- @ref llm::parse_safetensors() - Parse HuggingFace SafeTensors format
- @ref llm::kv_cache_append() - Append new tokens to KV cache
- @ref llm::kv_cache_rotate() - Sliding window cache rotation
- @ref llm::InferenceEngine::beam_search() - Beam search decoding

## References

- [SafeTensors Format Specification](https://huggingface.co/docs/safetensors)
- [Beam Search (Wu et al., 2016)](https://arxiv.org/abs/1609.08144)
- [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) - Chapters 4-5
