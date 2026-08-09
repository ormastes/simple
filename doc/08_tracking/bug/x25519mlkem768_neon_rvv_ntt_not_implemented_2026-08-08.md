# NEON and RVV ML-KEM NTT candidates are declared but have no vector kernel

**Status:** OPEN — fail-closed; do not promote ARM or RISC-V SIMD.

**Scope:** `X25519MLKEM768` candidate execution on AArch64 NEON and RISC-V V.

`src/lib/nogc_sync_mut/simd.spl:767` implements only the AVX2 i32x8 NTT
butterfly path.  It returns an empty batch unless `has_avx2()` is true, and
`mlkem_ntt_simd_backend()` therefore returns only `1` (AVX2) or `0` (no
executed SIMD kernel).  `execution_policy.spl` correctly requires code `2`
for NEON and `3` for RVV, so both requested candidates reject rather than
misrepresent scalar work as SIMD evidence.

The native profile now reports NEON/RVV capability accurately, but capability
is not execution proof.  The required completion work is:

1. Implement byte-identical NEON and RVV butterfly kernels over the pinned
   256-coefficient ML-KEM polynomial input.
2. Emit only actual chunk counts; RVV must record observed VLEN (at least 128,
   divisible by 32).
3. Add native same-fixture scalar-vs-NEON/RVV Set A/B/C tests and retained
   timing receipts with at least 30 measured samples.
4. Run each lane on physical AArch64 and RISC-V hosts before promotion.

No configuration-only or synthetic measurement can close this issue.
