# Tokenization and Embeddings

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** Token embedding lookup on GPU

## Simple Approach

Simple uses the `~>` pipeline operator to express the embedding layer as part of a
composable neural network pipeline. The embedding lookup itself is a GPU kernel that
maps token IDs to dense vectors.

Key features:
- **Pipeline syntax:** `tokens ~> Embedding(vocab_size, embed_dim)` connects layers
- **Dimension checking:** Compile-time validation that tensor shapes match between layers
- **Batch support:** Automatic batching of token sequences
- **GPU-backed lookup:** Embedding table stored in GPU memory for fast access

## Concepts Covered

- Token ID to embedding vector lookup kernel
- Embedding table initialization (random, pretrained)
- Batched embedding lookup
- Position embeddings
- Pipeline composition with `~>`

## Files

- `main.spl` - Embedding lookup kernel and pipeline
- `spec.spl` - Tests for embedding operations
