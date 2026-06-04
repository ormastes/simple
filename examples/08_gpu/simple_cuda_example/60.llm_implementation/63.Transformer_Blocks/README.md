# Transformer Blocks

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** Full transformer block: attention + FFN + layer norm + residual connections

## Simple Approach

Simple uses the `~>` pipeline operator to compose transformer blocks from individual
layers. Each sub-layer (attention, FFN, layer norm) is a composable unit that can be
connected into a pipeline with automatic dimension propagation.

Key features:
- **Pipeline composition:** `attention ~> LayerNorm ~> FFN ~> LayerNorm`
- **Residual connections:** Built-in `Residual(sublayer)` wrapper
- **Layer norm kernel:** GPU-accelerated normalization
- **GELU activation:** GPU kernel for the feed-forward network

## Concepts Covered

- Layer normalization on GPU
- Feed-forward network (two linear layers + GELU)
- Residual (skip) connections
- Full transformer block assembly
- Pipeline composition with `~>`

## Files

- `main.spl` - Transformer block with attention, FFN, layer norm
- `spec.spl` - Tests for transformer block components
