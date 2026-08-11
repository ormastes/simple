# X25519MLKEM768 architecture — TLDR

```sdn
capsule: {
  contract: versioned_typed_config_evidence,
  core: scalar_validated_constant_time,
  cpu: [scalar, avx2, neon, rvv],
  gpu_batch: [cuda, vulkan, metal],
  tls: [client, server]
}
```

- Scalar owns semantics; external free modules are test oracles only.
- SIMD specializes narrow ML-KEM kernels behind one facade.
- GPU adapters are persistent batch providers; TLS normally uses scalar/SIMD.
- Exact wire order: client `ek||X`, server `ct||X`, secret `K||X`.
- Suggest records fallback; Require fails closed.
- Cache keys bind profile, backend, device, source, artifact, config, and semantic version.
- Native AVX2/CUDA/Vulkan are local; NEON/RVV/Metal need external-host proof.
- Incremental C gcov uses four source-bound SIMD lanes and a retained zero-hit
  denominator; merged output is diagnostic until the merger binds that denominator.
- Timed receipt v3 binds native SIMD hits per sample, preventing aggregate hits
  from concealing a fallback ordinal.
