# X25519MLKEM768 test plan — TLDR

```sdn
sets: {
  unit: official_kat_negative,
  integration: same_fixture_backend_config,
  system: tls_interop_failure_paths,
  perf: promotion_break_even
}
```

- Unit: official ACVP/RFC vectors and malformed/implicit-rejection cases.
- Integration: scalar vs AVX2/NEON/RVV/CUDA/Vulkan/Metal on identical bytes/config.
- System: TLS client/server/HRR/alert/interoperability, entropy, and an
  above-1460-byte hybrid ClientHello with no silent downgrade.
- Perf: scalar regression, SIMD 1.5x, GPU 1.25x end-to-end break-even.
- Coverage target: calibrated measured 98% overall and 100% critical; current measured evidence is still missing.
- All REQ-001..017 have at least three tagged cases and no placeholder/skip scenarios.
- Injected ISA receipts cover AVX2/NEON/RVV policy branches only, never native execution.
- Hosted HTTPS, native Vulkan ML-KEM, live TLS interop, and cache-invalidation execution remain open; Go 1.24, CIRCL v1.6.4, and OpenSSL 3.5.7 key/decapsulation parity pass.
- Native ARM/RVV/Metal rows remain blockers until prepared-host evidence exists.
