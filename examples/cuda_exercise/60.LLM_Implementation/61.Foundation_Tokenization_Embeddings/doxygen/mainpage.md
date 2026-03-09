# Module 61: Foundation - Tokenization and Embeddings

## Overview

This module implements tokenization and embedding layers for transformer-based language models, providing the foundation for converting text into numerical representations that can be processed by neural networks.

Based on "LLMs from Scratch" by Sebastian Raschka (Chapter 2).

## Architecture

The module is organized into the following components:

### Tokenizers (host/)
- **SimpleTokenizerV1**: Basic regex-based word tokenizer
- **SimpleTokenizerV2**: Extended tokenizer with special tokens (`<|unk|>`, `<|pad|>`, `<|bos|>`, `<|eos|>`)
- **BPETokenizer**: Byte-Pair Encoding subword tokenizer

### Embeddings (kernels/)
- **TokenEmbedding**: Learned lookup table mapping token IDs to dense vectors
- **PositionalEncoding**: Injects sequence order information (sinusoidal or learned)
- **EmbeddingLayer**: Combined token + positional embeddings

### Utilities (common/)
- Vocabulary management
- Text preprocessing
- Shared data structures

## Key APIs

### Tokenization

- @ref SimpleTokenizerV1::BuildVocab() - Build vocabulary from text corpus
- @ref SimpleTokenizerV1::Encode() - Convert text to token IDs
- @ref SimpleTokenizerV1::Decode() - Convert token IDs back to text
- @ref SimpleTokenizerV2::PadSequence() - Pad sequence to fixed length
- @ref BPETokenizer::Train() - Train BPE merges on corpus

### Embeddings

- @ref TokenEmbedding::Forward() - Lookup token embeddings
- @ref SinusoidalPositionalEncoding::AddPositionalEncoding() - Add position info
- @ref LearnedPositionalEmbedding::AddPositionalEncoding() - Add learned positions
- @ref EmbeddingLayer::Forward() - Complete embedding pipeline

## Usage Examples

### Tokenization Example

```cpp
#include "host/simple_tokenizer_v2.h"

// Create tokenizer
SimpleTokenizerV2 tokenizer;

// Build vocabulary
std::string corpus = "Hello world! This is a test.";
tokenizer.BuildVocab(corpus);

// Encode text
std::vector<int> ids = tokenizer.Encode("Hello world!", true, true);
// Result: [<BOS>, "Hello", " ", "world", "!", <EOS>]

// Decode back to text
std::string text = tokenizer.Decode(ids);
```

### Embedding Example

```cpp
#include "common/embedding_layer.h"

// Create embedding layer
// vocab_size=50257, max_seq_len=1024, embed_dim=768
EmbeddingLayer embedding(50257, 1024, 768);

// Input token IDs (on GPU)
int* d_token_ids;  // [batch=2, seq_len=10]
float* d_output;   // [2, 10, 768]

// Forward pass
embedding.Forward(d_token_ids, d_output, 2, 10);

// Result: d_output contains token embeddings + positional encodings
```

## Testing

Comprehensive unit tests are available in `test/unit/`:
- `test_simple_tokenizer_v1.cpp`: SimpleTokenizerV1 tests
- `test_simple_tokenizer_v2.cpp`: SimpleTokenizerV2 tests
- `test_bpe_tokenizer.cpp`: BPE tokenizer tests
- `test_token_embedding.cu`: Token embedding kernel tests
- `test_positional_encoding.cu`: Positional encoding tests
- `test_embedding_layer.cu`: Complete embedding layer tests

## Performance

Expected performance on RTX 3090:

| Component | Input Size | Throughput |
|-----------|-----------|------------|
| Token Embedding | [32, 512] | ~2M tokens/sec |
| Positional Encoding | [32, 512] | ~10M positions/sec |
| Complete Layer | [32, 512] | ~1.8M tokens/sec |

## References

- [LLMs from Scratch](https://github.com/rasbt/LLMs-from-scratch) - Base reference
- [BPE Paper](https://arxiv.org/abs/1508.07909) - Byte-Pair Encoding
- [Attention Is All You Need](https://arxiv.org/abs/1706.03762) - Transformer paper
