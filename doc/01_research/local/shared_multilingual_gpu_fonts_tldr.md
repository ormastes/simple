# Shared Multilingual GPU Fonts — Local Research TLDR

> Historical pre-selection snapshot. Current selected state and evidence limits
> are authoritative in `doc/02_requirements/feature/shared_multilingual_gpu_fonts.md`
> and `doc/07_guide/lib/shared_multilingual_gpu_fonts.md`.

- Reuse `FontRenderer`, Pure Simple shaping/BiDi, `gpu_portable_compute.spl`, Engine2D, and device-evidence contracts.
- Current multilingual registry has an implicit/stale language set and no immutable asset provenance/checksums.
- Metal alone has genuine fixed-5x7 atlas GPU composition.
- CUDA/HIP/Vulkan/WebGPU text is CPU-raster/blit or unwired; 3D atlas is metadata-only.
- No implementation or font binary import is authorized before option selection.

```text
font manifest + shaping -> shared renderer -> portable emitter -> 2D / 3D -> honest device evidence
```
