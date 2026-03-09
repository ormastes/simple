# GPT Architecture

**Tier:** 2 (Concept Adaptation)
**Original CUDA Concept:** Complete GPT model assembly from transformer blocks

## Simple Approach

Simple assembles GPT from composable transformer blocks using the `~>` pipeline
operator. The architecture follows the standard GPT pattern: token embeddings +
positional encoding -> N transformer blocks -> layer norm -> linear projection.

Key features:
- **Pipeline assembly:** Entire model expressed as a `~>` chain
- **Configurable depth:** Variable number of transformer blocks
- **Weight initialization:** Built-in initialization schemes
- **Causal attention:** Autoregressive masking built into attention layers

## Concepts Covered

- GPT model configuration (layers, heads, dimensions)
- Stacked transformer blocks
- Token + positional embedding
- Final layer norm and output projection
- Top-k / top-p sampling
- Full forward pass on GPU

## Files

- `main.spl` - Complete GPT architecture with forward pass
- `spec.spl` - Tests for GPT model structure and output shapes
