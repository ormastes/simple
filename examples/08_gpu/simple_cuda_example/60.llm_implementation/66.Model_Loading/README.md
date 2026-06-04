# Model Loading and Inference

**Tier:** 3 (Skip)
**Status:** Covered elsewhere in Simple

## Why Skipped

Model loading (weight deserialization, format conversion, quantization) and inference
serving are application-level concerns covered by Simple's standard library and tooling
rather than being GPU kernel exercises.

Key Simple resources for model loading/inference:
- **SMF format:** Simple's native model serialization format (see `src/compiler/80.driver/`)
- **`std.ml.Tensor`:** Built-in tensor loading and format conversion
- **Exercise 64 (GPT Architecture):** Complete model with forward pass
- **Exercise 38 (Tensor Cores):** Mixed-precision inference with f16

## Original CUDA Exercise

See the original model loading exercise for CUDA-specific weight loading, GGUF/safetensors
parsing, and quantized inference kernels.

**Reference:** For Simple's model format, see `doc/architecture/glossary.md` (SMF entry)
and the serialization code in `src/compiler/80.driver/`.
