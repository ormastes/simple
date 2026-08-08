# X25519MLKEM768 requirements — TLDR

```sdn
selection: D
profile: { fips: 203, tls_group: 0x11ec, tls_draft: ecdhe_mlkem_05 }
backends: [scalar, avx2, neon, rvv, cuda, vulkan, metal]
tests: [official_kat_negative, same_fixture_backend_diff, tls_system_interop]
```

- Exact standardized wire and secret ordering, typed validation, and fail-closed TLS alerts.
- Scalar is the in-tree oracle; mlkem-native and official ACVP vectors are independent references.
- SIMD specializes AVX2, NEON, and vector-length-agnostic RVV.
- CUDA/Vulkan/Metal are persistent batch-first lanes with real device readback.
- Suggest records fallback; Require never falls back.
- External-host rows remain blocked until native evidence exists.

