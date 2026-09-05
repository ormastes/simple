# X25519MLKEM768 domain research — TLDR

```sdn
standard: { ml_kem: FIPS_203, tls: draft_ietf_tls_ecdhe_mlkem_05, group: 0x11ec }
wire: { client: mlkem_ek_then_x25519, server: mlkem_ct_then_x25519, secret: mlkem_then_x25519 }
oracle: mlkem_native
```

- Pin FIPS/profile and TLS draft versions; NIST lists a pending FIPS 203 erratum.
- Use official ACVP vectors plus mlkem-native as the primary independent oracle.
- CIRCL, current Go, and OpenSSL 3.5 provide secondary differential/interoperability checks.
- SIMD should specialize narrow kernels for AVX2, NEON, and vector-length-agnostic RVV.
- GPU is a persistent batch lane, not a presumed single-handshake optimization.
- cuPQC is a performance reference, not a reusable FOSS production module.
- Vulkan/Metal ML-KEM lack authoritative maintained prior art and require experimental fail-closed evidence.
- Draft `-05` is in late IETF processing and now marks X25519MLKEM768 Recommended Y; it is still not an RFC.
- Go defaults to the group from 1.24 and OpenSSL 3.5 puts it first; retain a fragmented/large-ClientHello interoperability row.
## GCC denominator update

- GCC 13.3 `gcov -j -b -c` provides JSON branch arcs and exact counts.
- Cross-target GCC/gcov pairs supply the compiled x86, AArch64, and RVV
  denominators.
- Gcov arcs cannot be reliably mapped back to individual source expressions;
  they are counted as branch outcomes, not claimed as MC/DC.
- Explicit high-bit runtime IDs remain authoritative for critical SIMD gates.
